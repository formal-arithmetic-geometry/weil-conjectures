/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q159
-/
module

public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Subterminal
import all Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.Tactic.CategoryTheory.Slice
import all Sheaf.Paper.ConstantCompletionEquivalence
import all Sheaf.Paper.ConstantCompletionCore
import all Sheaf.Paper.ConstantCompletionInverseImage

/-! # Scalar change and the normalized inverse-exchange adjunct

Source: main-20261015, sk-thm-purity-transport.proof.md, Steps 1 and 3;
Stacks 07A4, 0D6D, 07A7 and 0GL1.
(blueprint: lem-pur-topos-scalar-inverse-exchange-mate).

Presentation records retain ordinary sheaf functors and the universal cochain comparisons.
The pure-insertion equations specify the ordinary comparisons. Their resolving equations
specify the derived comparisons, rather than arbitrary isomorphisms of the same endpoints.
All derived categories below are ordinary unbounded localizations of module sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion

attribute [local irreducible] ConstantCompletion.change ConstantCompletion.extend
  ConstantCompletion.pull ConstantCompletion.derivedExtension
  ConstantCompletion.derivedPull HasDerivedCategory.standard

namespace CategoryTheory.ToposScalarInverseExchange

/-- A fixed small-site presentation in the universe of module sheaves.
Source: Stacks 00XA (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
structure Presentation where
  C : Type u
  [category : SmallCategory C]
  J : GrothendieckTopology C

attribute [instance] Presentation.category

/-- The actual constant ring sheaf in a presentation.
Source: Stacks 093M (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
abbrev Presentation.ring (X : Presentation.{u}) (R : Type u) [CommRing R] :=
  constant X.J R

/-- The ordinary unbounded derived category of module sheaves over the constant ring.
Source: Stacks 05RR (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
abbrev Presentation.derived (X : Presentation.{u}) (R : Type u) [CommRing R] :=
  D (X.ring R)

/-- The ring map on constant sheaves.
Source: Stacks 093M (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
def Presentation.scalarMap (X : Presentation.{u}) {A B : Type u}
    [CommRing A] [CommRing B] (φ : A →+* B) : X.ring A ⟶ X.ring B :=
  (constantSheaf X.J CommRingCat.{u}).map (CommRingCat.ofHom φ)

/-- The specified universal derived extension of scalars, with its K-flat counit.
Source: Stacks 06YY (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
abbrev Presentation.scalar (X : Presentation.{u}) {A B : Type u}
    [CommRing A] [CommRing B] (φ : A →+* B) := extend (X.scalarMap φ)

/-- A geometric morphism and its algebraic lifts. The latter retain all ring and
module generalized-element equations and the canonical constant-ring comparison.
Source: Stacks 00YV, 03D2 (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
structure Geometric (X W : Presentation.{u}) extends
    GeometricMorphism (Sheaf X.J (Type u)) (Sheaf W.J (Type u)) where
  algebra : InverseImageData inverse

attribute [instance] GeometricMorphism.leftExact

attribute [local irreducible] Presentation.scalarMap

/-- Ordinary inverse image with the canonical constant-coefficient identification.
Source: Stacks 03D2 (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
abbrev Geometric.modules {X W : Presentation.{u}} (v : Geometric X W)
    (R : Type u) [CommRing R] := pull v.algebra (constantMap v.algebra R)

/-- The insertion identifying inverse image of a constant-coefficient module.
Source: Stacks 03D2 (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
abbrev Geometric.insertion {X W : Presentation.{u}} (v : Geometric X W)
    (R : Type u) [CommRing R] (M : Mod (W.ring R)) :=
  pullInsertion v.algebra (constantMap v.algebra R) M

/-- Open inclusion means a slice at a subterminal object. The inverse image is the
product-to-slice functor, transported through the fixed presentation equivalence.
Source: Stacks 00YV (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
structure Open {X W : Presentation.{u}} (j : Geometric X W) where
  object : Sheaf W.J (Type u)
  subterminal : IsSubterminal object
  presentation : Sheaf X.J (Type u) ≌ Over object
  restriction : j.inverse ⋙ presentation.functor ≅ Over.star object

/-- The ordinary module adjunction and its universal derived adjunction. The counit
square fixes the derived adjunction to the ordinary transpose; it prevents a change
of normalization of units or counits. The inverse image is exact, so its cochain
comparison is invertible on all complexes. The right comparison computes on K-injectives.
Source: Stacks 06YY, 09T5 (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
structure Image {X W : Presentation.{u}} (v : Geometric X W)
    (R : Type u) [CommRing R] where
  left : DerivedPull v.algebra (constantMap v.algebra R)
  exactComparison : IsIso left.comparison
  ordinaryRight : Mod (X.ring R) ⥤ Mod (W.ring R)
  [ordinaryAdditive : ordinaryRight.Additive]
  ordinaryAdj : v.modules R ⊣ ordinaryRight
  right : X.derived R ⥤ W.derived R
  comparison : ordinaryRight.mapHomologicalComplex (.up ℤ) ⋙ Q (W.ring R) ⟶
    Q (X.ring R) ⋙ right
  universal : right.IsRightDerivedFunctor comparison
    (HomologicalComplex.quasiIso (Mod (X.ring R)) (.up ℤ))
  computes : ∀ P : Cx (X.ring R), P.IsKInjective → IsIso (comparison.app P)
  adj : left.functor ⊣ right
  counit : ∀ P : Cx (X.ring R),
    left.functor.map (comparison.app P) ≫ adj.counit.app ((Q (X.ring R)).obj P) =
      left.comparison.app ((ordinaryRight.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (Q (X.ring R)).map ((ordinaryAdj.mapHomologicalComplex (.up ℤ)).counit.app P)

attribute [instance] Image.ordinaryAdditive

/-- The ordinary tensor/pullback comparison on inverse-image tensor generators.
Source: Stacks 07A4 (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
def ScalarPure {X W : Presentation.{u}} (v : Geometric X W)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (ordinary : change (W.scalarMap φ) ⋙ v.modules B ≅
      v.modules A ⋙ change (X.scalarMap φ)) : Prop :=
  ∀ M : Mod (W.ring A),
    v.inverse.map (ConstantCompletion.insertion (W.scalarMap φ) M) ≫
        v.insertion B ((change (W.scalarMap φ)).obj M) ≫
        (underlying (X.ring B)).map (ordinary.hom.app M) =
      v.insertion A M ≫ ConstantCompletion.insertion (X.scalarMap φ) ((v.modules A).obj M)

/-- The derived tensor/pullback comparison on flat-term K-flat representatives.
Source: Stacks 07A4 and 0D6D (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
def ScalarResolving {X W : Presentation.{u}} (v : Geometric X W)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (a : Image v A) (b : Image v B)
    (ordinary : change (W.scalarMap φ) ⋙ v.modules B ≅
      v.modules A ⋙ change (X.scalarMap φ))
    (derived : W.scalar φ ⋙ b.left.functor ≅ a.left.functor ⋙ X.scalar φ) : Prop :=
  ∀ (P : Cx (W.ring A)), P.IsAcyclicTensorKFlat →
    (∀ n : ℤ, SheafOfModules.IsFlat (J := W.J) (P.X n)) →
    derived.hom.app ((Q (W.ring A)).obj P) ≫
        (X.scalar φ).map (a.left.comparison.app P) ≫
        (extendComparison (X.scalarMap φ)).app
          (((v.modules A).mapHomologicalComplex (.up ℤ)).obj P) =
      b.left.functor.map ((extendComparison (W.scalarMap φ)).app P) ≫
        b.left.comparison.app
          (((change (W.scalarMap φ)).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (Q (X.ring B)).map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)

/-- Canonical tensor/pullback comparison with its ordinary and derived normalizations.
The two predicates specify the actual comparison, rather than any isomorphism of endpoints.
Source: Stacks 07A4 and 0D6D (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
structure ScalarComparison {X W : Presentation.{u}} (v : Geometric X W)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (a : Image v A) (b : Image v B) where
  ordinary : change (W.scalarMap φ) ⋙ v.modules B ≅ v.modules A ⋙ change (X.scalarMap φ)
  pure : ScalarPure v φ ordinary
  derived : W.scalar φ ⋙ b.left.functor ≅ a.left.functor ⋙ X.scalar φ
  resolving : ScalarResolving v φ a b ordinary derived

/-- A commuting Cartesian open square in fixed small presentations. The last
isomorphism expresses that the upper open is the inverse image of the lower open.
Source: purity-transport Steps 1, 3
(blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
structure Square where
  V : Presentation.{u}
  T : Presentation.{u}
  Y : Presentation.{u}
  Z : Presentation.{u}
  b : Geometric V T
  i : Geometric Y Z
  r : Geometric V Y
  p : Geometric T Z
  openB : Open b
  openI : Open i
  inverseSquare : i.inverse ⋙ r.inverse ≅ p.inverse ⋙ b.inverse
  cartesian : p.inverse.obj openI.object ≅ openB.object

/-- The inverse-image square comparison on generalized module generators.
Source: Stacks 03D2 and 07A4 (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
def SquarePure (s : Square.{u}) (R : Type u) [CommRing R]
    (ordinarySquare : s.i.modules R ⋙ s.r.modules R ≅ s.p.modules R ⋙ s.b.modules R) :
    Prop :=
  ∀ M : Mod (s.Z.ring R),
    s.r.inverse.map (s.i.insertion R M) ≫ s.r.insertion R ((s.i.modules R).obj M) ≫
        (underlying (s.V.ring R)).map (ordinarySquare.hom.app M) =
      s.inverseSquare.hom.app ((underlying (s.Z.ring R)).obj M) ≫
        s.b.inverse.map (s.p.insertion R M) ≫ s.b.insertion R ((s.p.modules R).obj M)

/-- The canonical derived inverse-image square on flat-term K-flat representatives.
Source: Stacks 0D6D (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
def SquareResolving (s : Square.{u}) (R : Type u) [CommRing R]
    (b : Image s.b R) (i : Image s.i R) (r : Image s.r R) (p : Image s.p R)
    (ordinarySquare : s.i.modules R ⋙ s.r.modules R ≅ s.p.modules R ⋙ s.b.modules R)
    (square : i.left.functor ⋙ r.left.functor ≅ p.left.functor ⋙ b.left.functor) : Prop :=
  ∀ (P : Cx (s.Z.ring R)), P.IsAcyclicTensorKFlat →
    (∀ n : ℤ, SheafOfModules.IsFlat (J := s.Z.J) (P.X n)) →
    square.hom.app ((Q (s.Z.ring R)).obj P) ≫
        b.left.functor.map (p.left.comparison.app P) ≫
        b.left.comparison.app (((s.p.modules R).mapHomologicalComplex (.up ℤ)).obj P) =
      r.left.functor.map (i.left.comparison.app P) ≫
        r.left.comparison.app (((s.i.modules R).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (Q (s.V.ring R)).map ((NatIso.mapHomologicalComplex ordinarySquare (.up ℤ)).hom.app P)

/-- Operations over one coefficient ring. The ordinary inverse-image square is fixed
on generalized generators by the geometric square, and its derived square is fixed
on resolving complexes. Open extension is the left adjoint to exact open restriction;
this universal property determines its functor and actual unit up to unique compatible
isomorphism. Its invertible unit records full faithfulness.
Source: Stacks 03DI, 0D6D (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
structure Operations (s : Square.{u}) (R : Type u) [CommRing R] where
  b : Image s.b R
  i : Image s.i R
  r : Image s.r R
  p : Image s.p R
  ordinarySquare : s.i.modules R ⋙ s.r.modules R ≅ s.p.modules R ⋙ s.b.modules R
  pure : SquarePure s R ordinarySquare
  square : i.left.functor ⋙ r.left.functor ≅ p.left.functor ⋙ b.left.functor
  resolving : SquareResolving s R b i r p ordinarySquare square
  extendB : s.V.derived R ⥤ s.T.derived R
  extendI : s.Y.derived R ⥤ s.Z.derived R
  openAdjB : extendB ⊣ b.left.functor
  openAdjI : extendI ⊣ i.left.functor
  [unitB : IsIso openAdjB.unit]
  [unitI : IsIso openAdjI.unit]

attribute [instance] Operations.unitB Operations.unitI

/-- The specified inverse-image exchange, using the dependency's actual mate operation.
Source: Stacks 07A7 (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
def Operations.exchange {s : Square.{u}} {R : Type u} [CommRing R]
    (o : Operations s R) : o.p.right ⋙ o.i.left.functor ⟶ o.b.left.functor ⋙ o.r.right :=
  (mateEquiv o.p.adj o.r.adj (TwoSquare.mk _ _ _ _ o.square.hom)).natTrans

/-- The exchange followed by the inverse of the actual open unit.
Source: purity-transport inverse-exchange normalization
(blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
def Operations.t {s : Square.{u}} {R : Type u} [CommRing R]
    (o : Operations s R) (M : s.V.derived R) :
    o.i.left.functor.obj (o.p.right.obj (o.extendB.obj M)) ⟶ o.r.right.obj M :=
  o.exchange.app (o.extendB.obj M) ≫ o.r.right.map (inv (o.openAdjB.unit.app M))

/-- The specified open adjunct of inverse exchange. Only its own t component is inverted.
Source: purity-transport Steps 1, 3
(blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
def Operations.gamma {s : Square.{u}} {R : Type u} [CommRing R]
    (o : Operations s R) (M : s.V.derived R) [IsIso (o.t M)] :
    o.extendI.obj (o.r.right.obj M) ⟶ o.p.right.obj (o.extendB.obj M) :=
  (o.openAdjI.homEquiv _ _).symm (inv (o.t M))

/-- The scalar/direct-image mate of the canonical tensor/pullback comparison.
Source: Stacks 07A7 (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
def ScalarComparison.chi {X W : Presentation.{u}} {v : Geometric X W}
    {A B : Type u} [CommRing A] [CommRing B] {φ : A →+* B}
    {a : Image v A} {b : Image v B} (c : ScalarComparison v φ a b) :
    a.right ⋙ W.scalar φ ⟶ X.scalar φ ⋙ b.right :=
  (mateEquiv a.adj b.adj (TwoSquare.mk _ _ _ _ c.derived.hom)).natTrans

/-- Scalar data over the square. Each open balancing inverse is its specified
adjunction mate of inverse lambda. This is the equivalent adjunct characterization
of the canonical balancing map in lem-pur-topos-open-scalar-unit; it uniquely fixes
that map, including the units, and does not impose either exchange identity.
Source: Stacks 03DI, 07A4 (blueprint: lem-pur-topos-scalar-inverse-exchange-mate). -/
structure Scalars (s : Square.{u}) {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (a : Operations s A) (b : Operations s B) where
  atB : ScalarComparison s.b φ a.b b.b
  atI : ScalarComparison s.i φ a.i b.i
  atR : ScalarComparison s.r φ a.r b.r
  atP : ScalarComparison s.p φ a.p b.p
  betaB : a.extendB ⋙ s.T.scalar φ ≅ s.V.scalar φ ⋙ b.extendB
  betaI : a.extendI ⋙ s.Z.scalar φ ≅ s.Y.scalar φ ⋙ b.extendI
  betaB_mate :
    (mateEquiv a.openAdjB b.openAdjB (TwoSquare.mk _ _ _ _ betaB.inv)).natTrans =
      atB.derived.inv
  betaI_mate :
    (mateEquiv a.openAdjI b.openAdjI (TwoSquare.mk _ _ _ _ betaI.inv)).natTrans =
      atI.derived.inv

private theorem scalar_insertion_natural {X : Presentation.{u}}
    {R S : Sheaf X.J CommRingCat.{u}} (φ : R ⟶ S) {M N : Mod R} (f : M ⟶ N) :
    (underlying R).map f ≫ ConstantCompletion.insertion φ N =
      ConstantCompletion.insertion φ M ≫ (underlying S).map ((change φ).map f) := by
  ext U m
  change (ConstantCompletion.insertion φ N).hom.app U (f.val.app U m) =
    ((change φ).map f).val.app U ((ConstantCompletion.insertion φ M).hom.app U m)
  rw [show (ConstantCompletion.insertion φ N).hom.app U (f.val.app U m) =
    tensorSection φ N U 1 (f.val.app U m) from
      (insertion_existsUnique φ N).exists.choose_spec U (f.val.app U m),
    show (ConstantCompletion.insertion φ M).hom.app U m = tensorSection φ M U 1 m from
      (insertion_existsUnique φ M).exists.choose_spec U m]
  exact (tensorSection_map φ f U 1 m).symm

attribute [local semireducible] ConstantCompletion.change ConstantCompletion.pull

private theorem scalar_insertion_ext {X : Presentation.{u}}
    {R S : Sheaf X.J CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R) (N : Mod S)
    {f g : (change φ).obj M ⟶ N}
    (h : ConstantCompletion.insertion φ M ≫ (underlying S).map f =
      ConstantCompletion.insertion φ M ≫ (underlying S).map g) : f = g := by
  change (show (SheafOfModules.RingedTensor.tensorFunctor φ).obj M ⟶ N from f) = g
  apply (SheafOfModules.RingedTensor.tensorHomEquiv φ M N).injective
  ext U m
  have hh := congrFun (congrArg (fun z ↦ z.hom.app U) h) m
  change f.val.app U ((ConstantCompletion.insertion φ M).hom.app U m) =
    g.val.app U ((ConstantCompletion.insertion φ M).hom.app U m) at hh
  rw [show (ConstantCompletion.insertion φ M).hom.app U m =
    tensorSection φ M U 1 m from (insertion_existsUnique φ M).exists.choose_spec U m] at hh
  exact hh

private theorem scalar_restriction_equivalence
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{u} c.hom).IsEquivalence := by
  let ec : C ≌ C := Equivalence.refl
  have : ec.functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  have : ec.inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let e := SheafOfModules.pushforwardPushforwardEquivalence (J := J) (K := J)
    ec c.hom c.inv
    (by
      ext U x
      dsimp [ec, Equivalence.refl]
      simp only [Functor.map_id]
      exact congrArg (fun f : S ⟶ S ↦ f.hom.app U x) c.inv_hom_id.symm)
    (by
      ext U x
      dsimp [ec, Equivalence.refl]
      simp only [Functor.map_id]
      exact congrArg (fun f : R ⟶ R ↦ f.hom.app U x) c.hom_inv_id)
  have h : SheafOfModules.restrictScalars.{u} c.hom = e.functor := by rfl
  rw [h]
  exact e.isEquivalence_functor

private theorem geometric_insertion_iso {X W : Presentation.{u}} (v : Geometric X W)
    (R : Type u) [CommRing R] (M : Mod (W.ring R)) : IsIso (v.insertion R M) := by
  have : (SheafOfModules.restriction
      (constantMap v.algebra R)).IsEquivalence :=
    scalar_restriction_equivalence
      ((sheafCompose X.J (forget₂ CommRingCat RingCat)).mapIso
        (v.algebra.constants.app (CommRingCat.of R)))
  have := (SheafOfModules.tensorAdjunction
    (constantMap v.algebra R)).isEquivalence_left_of_isEquivalence_right
  have hi : ConstantCompletion.insertion (constantMap v.algebra R)
      ((v.algebra.algebra (W.ring R)).modules.obj M) =
      SheafOfModules.tensorUnit (constantMap v.algebra R)
        ((v.algebra.algebra (W.ring R)).modules.obj M) := by
    ext U m
    exact ((insertion_existsUnique _ _).exists.choose_spec U m).trans
      (SheafOfModules.tensorUnit_apply _ _ U m).symm
  dsimp only [Geometric.insertion, pullInsertion]
  rw [hi]
  dsimp only [SheafOfModules.tensorUnit]
  infer_instance

private theorem geometric_insertion_natural {X W : Presentation.{u}} (v : Geometric X W)
    (R : Type u) [CommRing R] {M N : Mod (W.ring R)} (f : M ⟶ N) :
    v.inverse.map ((underlying (W.ring R)).map f) ≫ v.insertion R N =
      v.insertion R M ≫ (underlying (X.ring R)).map ((v.modules R).map f) := by
  have ha := (v.algebra.algebra (W.ring R)).moduleUnderlying.inv.naturality f
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at ha
  have hb := scalar_insertion_natural (X := X) (constantMap v.algebra R)
    ((v.algebra.algebra (W.ring R)).modules.map f)
  dsimp only [Geometric.insertion, pullInsertion]
  erw [← Category.assoc, ha, Category.assoc, hb]
  rfl

attribute [local irreducible] ConstantCompletion.change

private theorem scalar_generator_cancel {X : Presentation.{u}}
    {R S : Sheaf X.J CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R) (N H : Mod S)
    (L : N ≅ (change φ).obj M) {Z : Sheaf X.J (Type u)}
    (η : Z ⟶ (underlying R).obj M) [IsIso η]
    (q : Z ⟶ (underlying S).obj N)
    (hq : q ≫ (underlying S).map L.hom = η ≫ ConstantCompletion.insertion φ M)
    {f g : N ⟶ H} (h : q ≫ (underlying S).map f = q ≫ (underlying S).map g) :
    f = g := by
  have hi : (η ≫ ConstantCompletion.insertion φ M) ≫ (underlying S).map L.inv = q := by
    rw [← hq, Category.assoc, ← Functor.map_comp, L.hom_inv_id, Functor.map_id,
      Category.comp_id]
  apply (cancel_epi L.inv).1
  apply scalar_insertion_ext (X := X) φ M H
  apply (cancel_epi η).1
  simpa only [Functor.map_comp, ← Category.assoc, hi] using h

private theorem ordinary_cube {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} {s : Square.{u}} {a : Operations s A} {b : Operations s B}
    (c : Scalars s φ a b) (M : Mod (s.Z.ring A)) :
    (s.r.modules B).map (c.atI.ordinary.hom.app M) ≫
        c.atR.ordinary.hom.app ((s.i.modules A).obj M) ≫
        (change (s.V.scalarMap φ)).map (a.ordinarySquare.hom.app M) =
      b.ordinarySquare.hom.app ((change (s.Z.scalarMap φ)).obj M) ≫
        (s.b.modules B).map (c.atP.ordinary.hom.app M) ≫
        c.atB.ordinary.hom.app ((s.p.modules A).obj M) := by
  let U := underlying (s.V.ring B)
  let L := (s.r.modules B).mapIso (c.atI.ordinary.app M) ≪≫
    c.atR.ordinary.app ((s.i.modules A).obj M)
  let η := s.r.inverse.map (s.i.insertion A M) ≫
    s.r.insertion A ((s.i.modules A).obj M)
  have := geometric_insertion_iso s.i A M
  have := geometric_insertion_iso s.r A ((s.i.modules A).obj M)
  have : IsIso η := by dsimp only [η]; infer_instance
  let q := s.r.inverse.map (s.i.inverse.map
      (ConstantCompletion.insertion (s.Z.scalarMap φ) M)) ≫
    s.r.inverse.map (s.i.insertion B ((change (s.Z.scalarMap φ)).obj M)) ≫
    s.r.insertion B ((s.i.modules B).obj ((change (s.Z.scalarMap φ)).obj M))
  have hq : q ≫ U.map L.hom = η ≫
      ConstantCompletion.insertion (s.V.scalarMap φ) ((s.r.modules A).obj
        ((s.i.modules A).obj M)) := by
    dsimp only [q, L, η, Iso.trans_hom, Functor.mapIso_hom]
    simp only [U, Functor.map_comp, Iso.app_hom, Category.assoc]
    slice_lhs 3 4 =>
      erw [← geometric_insertion_natural s.r B (c.atI.ordinary.hom.app M)]
    slice_lhs 1 3 =>
      rw [← s.r.inverse.map_comp, ← s.r.inverse.map_comp, c.atI.pure M,
        s.r.inverse.map_comp]
    simp only [Category.assoc]
    slice_lhs 2 4 => exact c.atR.pure ((s.i.modules A).obj M)
  apply scalar_generator_cancel (X := s.V) (s.V.scalarMap φ) _ _ _ L η q hq
  change (q ≫ U.map L.hom) ≫ U.map
      ((change (s.V.scalarMap φ)).map (a.ordinarySquare.hom.app M)) = _
  rw [hq]
  simp only [Category.assoc]
  rw [← scalar_insertion_natural (X := s.V)]
  dsimp only [η, q, U]
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 1 3 => rw [a.pure M]
  slice_rhs 2 4 => rw [b.pure]
  simp only [Category.assoc]
  slice_rhs 4 5 =>
    erw [← geometric_insertion_natural s.b B (c.atP.ordinary.hom.app M)]
  simp only [Category.assoc]
  have hn := s.inverseSquare.hom.naturality
    (ConstantCompletion.insertion (s.Z.scalarMap φ) M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  slice_rhs 1 2 => exact hn
  simp only [Category.assoc]
  slice_rhs 2 4 =>
    rw [← s.b.inverse.map_comp, ← s.b.inverse.map_comp, c.atP.pure M,
      s.b.inverse.map_comp]
  simp only [Category.assoc]
  slice_rhs 3 5 => exact c.atB.pure ((s.p.modules A).obj M)
  rfl


attribute [local semireducible] ConstantCompletion.extend

private theorem paste_left
    {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ E₁ E₂ Z Y₁ Y₂ Y₃ T₁ T₂ T₃ D₁ D₂ D₃ : C}
    {l₁ : X₀ ⟶ X₁} {l₂ : X₁ ⟶ X₂} {l₃ : X₂ ⟶ X₃}
    {e₁ : X₃ ⟶ E₁} {e₂ : E₁ ⟶ E₂} {e₃ : E₂ ⟶ Z}
    {x₁ : X₂ ⟶ Y₁} {x₂ : Y₁ ⟶ Y₂} {q₀ : Y₂ ⟶ E₂}
    {y₁ : X₁ ⟶ Y₃} {lam : Y₃ ⟶ Y₁} {eps : Y₂ ⟶ T₃}
    {rExt : Y₃ ⟶ T₂} {rcomp : T₂ ⟶ T₁} {qR : T₁ ⟶ T₃}
    {d₁ : X₀ ⟶ D₁} {d₂ : D₁ ⟶ D₂} {d₃ : D₂ ⟶ D₃}
    {rqI : D₂ ⟶ T₂} {qI : D₃ ⟶ T₁} {qA : T₃ ⟶ Z}
    (hA : l₃ ≫ e₁ ≫ e₂ = x₁ ≫ x₂ ≫ q₀)
    (hε : q₀ ≫ e₃ = eps ≫ qA)
    (hn : l₂ ≫ x₁ = y₁ ≫ lam)
    (hR : lam ≫ x₂ ≫ eps = rExt ≫ rcomp ≫ qR)
    (hI : l₁ ≫ y₁ ≫ rExt = d₁ ≫ d₂ ≫ rqI)
    (hQ : rqI ≫ rcomp = d₃ ≫ qI) :
    l₁ ≫ l₂ ≫ l₃ ≫ e₁ ≫ e₂ ≫ e₃ =
      d₁ ≫ d₂ ≫ d₃ ≫ qI ≫ qR ≫ qA := by
  slice_lhs 3 5 => rw [hA]
  simp only [Category.assoc]
  rw [hε]
  slice_lhs 2 3 => rw [hn]
  simp only [Category.assoc]
  slice_lhs 3 5 => rw [hR]
  simp only [Category.assoc]
  slice_lhs 1 3 => rw [hI]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [hQ]
  simp only [Category.assoc]

private theorem paste_right
    {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ E₁ E₂ Z Y₁ Y₂ N₁ N₂ T T₀ D₁ D₂ D₃ : C}
    {r₁ : X₀ ⟶ X₁} {r₂ : X₁ ⟶ X₂} {r₃ : X₂ ⟶ X₃}
    {e₁ : X₃ ⟶ E₁} {e₂ : E₁ ⟶ E₂} {e₃ : E₂ ⟶ Z}
    {y₁ : X₂ ⟶ Y₁} {lam : Y₁ ⟶ E₁} {cP : Y₁ ⟶ Y₂}
    {cB : Y₂ ⟶ T} {bB : T ⟶ Z}
    {bExt : X₁ ⟶ N₁} {bPc : N₁ ⟶ N₂} {bOrd : N₂ ⟶ Y₂}
    {d₁ : X₀ ⟶ D₁} {sq : D₁ ⟶ N₁} {bcomp : N₂ ⟶ T₀}
    {d₂ : D₁ ⟶ D₂} {d₃ : D₂ ⟶ D₃} {qS : D₃ ⟶ T₀} {qP : T₀ ⟶ T}
    (hn : r₃ ≫ e₁ = y₁ ≫ lam)
    (hB : lam ≫ e₂ ≫ e₃ = cP ≫ cB ≫ bB)
    (hP : r₂ ≫ y₁ ≫ cP = bExt ≫ bPc ≫ bOrd)
    (hN : r₁ ≫ bExt = d₁ ≫ sq)
    (hC : bOrd ≫ cB = bcomp ≫ qP)
    (hS : sq ≫ bPc ≫ bcomp = d₂ ≫ d₃ ≫ qS) :
    r₁ ≫ r₂ ≫ r₃ ≫ e₁ ≫ e₂ ≫ e₃ =
      d₁ ≫ d₂ ≫ d₃ ≫ qS ≫ qP ≫ bB := by
  slice_lhs 3 4 => rw [hn]
  simp only [Category.assoc]
  slice_lhs 4 6 => rw [hB]
  slice_lhs 2 4 => rw [hP]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [hN]
  simp only [Category.assoc]
  slice_lhs 4 5 => rw [hC]
  simp only [Category.assoc]
  slice_lhs 2 4 => rw [hS]
  simp only [Category.assoc]

private theorem representative_cube
    {H0 D0 : Type*} [Category H0] [Category D0]
    {H1 D1 : Type*} [Category H1] [Category D1]
    {H2 D2 : Type*} [Category H2] [Category D2]
    {H3 D3 : Type*} [Category H3] [Category D3]
    {H4 D4 : Type*} [Category H4] [Category D4]
    {H5 D5 : Type*} [Category H5] [Category D5]
    {H6 D6 : Type*} [Category H6] [Category D6]
    {H7 D7 : Type*} [Category H7] [Category D7]
    (q0 : H0 ⥤ D0)
    (q1 : H1 ⥤ D1)
    (q2 : H2 ⥤ D2)
    (q3 : H3 ⥤ D3)
    (q4 : H4 ⥤ D4)
    (q5 : H5 ⥤ D5)
    (q6 : H6 ⥤ D6)
    (q7 : H7 ⥤ D7)
    (f01 : H0 ⥤ H1) (d01 : D0 ⥤ D1)
    (f02 : H0 ⥤ H2) (d02 : D0 ⥤ D2)
    (f04 : H0 ⥤ H4) (d04 : D0 ⥤ D4)
    (f13 : H1 ⥤ H3) (d13 : D1 ⥤ D3)
    (f15 : H1 ⥤ H5) (d15 : D1 ⥤ D5)
    (f23 : H2 ⥤ H3) (d23 : D2 ⥤ D3)
    (f26 : H2 ⥤ H6) (d26 : D2 ⥤ D6)
    (f37 : H3 ⥤ H7) (d37 : D3 ⥤ D7)
    (f45 : H4 ⥤ H5) (d45 : D4 ⥤ D5)
    (f46 : H4 ⥤ H6) (d46 : D4 ⥤ D6)
    (f57 : H5 ⥤ H7) (d57 : D5 ⥤ D7)
    (f67 : H6 ⥤ H7) (d67 : D6 ⥤ D7)
    (e01 : q0 ⋙ d01 ⟶ f01 ⋙ q1)
    (e02 : q0 ⋙ d02 ⟶ f02 ⋙ q2)
    (e04 : q0 ⋙ d04 ⟶ f04 ⋙ q4)
    (e13 : q1 ⋙ d13 ⟶ f13 ⋙ q3)
    (e15 : q1 ⋙ d15 ⟶ f15 ⋙ q5)
    (e23 : q2 ⋙ d23 ⟶ f23 ⋙ q3)
    (e26 : q2 ⋙ d26 ⟶ f26 ⋙ q6)
    (e37 : q3 ⋙ d37 ⟶ f37 ⋙ q7)
    (e45 : q4 ⋙ d45 ⟶ f45 ⋙ q5)
    (e46 : q4 ⋙ d46 ⟶ f46 ⋙ q6)
    (e57 : q5 ⋙ d57 ⟶ f57 ⋙ q7)
    (e67 : q6 ⋙ d67 ⟶ f67 ⋙ q7)
    (oI : f01 ⋙ f13 ⟶ f02 ⋙ f23)
    (lI : d01 ⋙ d13 ⟶ d02 ⋙ d23)
    (oR : f23 ⋙ f37 ⟶ f26 ⋙ f67)
    (lR : d23 ⋙ d37 ⟶ d26 ⋙ d67)
    (oP : f01 ⋙ f15 ⟶ f04 ⋙ f45)
    (lP : d01 ⋙ d15 ⟶ d04 ⋙ d45)
    (oB : f45 ⋙ f57 ⟶ f46 ⋙ f67)
    (lB : d45 ⋙ d57 ⟶ d46 ⋙ d67)
    (oA : f02 ⋙ f26 ⟶ f04 ⋙ f46)
    (lA : d02 ⋙ d26 ⟶ d04 ⋙ d46)
    (oS : f13 ⋙ f37 ⟶ f15 ⋙ f57)
    (lS : d13 ⋙ d37 ⟶ d15 ⋙ d57)
    (P : H0)
    (hI : lI.app (q0.obj (P)) ≫ d23.map (e02.app (P)) ≫
      e23.app (f02.obj (P)) =
      d13.map (e01.app (P)) ≫ e13.app (f01.obj (P)) ≫
        q3.map (oI.app (P)))
    (hR : lR.app (q2.obj (f02.obj P)) ≫ d67.map (e26.app (f02.obj P)) ≫
      e67.app (f26.obj (f02.obj P)) =
      d37.map (e23.app (f02.obj P)) ≫ e37.app (f23.obj (f02.obj P)) ≫
        q7.map (oR.app (f02.obj P)))
    (hP : lP.app (q0.obj (P)) ≫ d45.map (e04.app (P)) ≫
      e45.app (f04.obj (P)) =
      d15.map (e01.app (P)) ≫ e15.app (f01.obj (P)) ≫
        q5.map (oP.app (P)))
    (hB : lB.app (q4.obj (f04.obj P)) ≫ d67.map (e46.app (f04.obj P)) ≫
      e67.app (f46.obj (f04.obj P)) =
      d57.map (e45.app (f04.obj P)) ≫ e57.app (f45.obj (f04.obj P)) ≫
        q7.map (oB.app (f04.obj P)))
    (hA : lA.app (q0.obj (P)) ≫ d46.map (e04.app (P)) ≫
      e46.app (f04.obj (P)) =
      d26.map (e02.app (P)) ≫ e26.app (f02.obj (P)) ≫
        q6.map (oA.app (P)))
    (hS : lS.app (q1.obj (f01.obj P)) ≫ d57.map (e15.app (f01.obj P)) ≫
      e57.app (f15.obj (f01.obj P)) =
      d37.map (e13.app (f01.obj P)) ≫ e37.app (f13.obj (f01.obj P)) ≫
        q7.map (oS.app (f01.obj P)))
    [IsIso (e04.app P)] [IsIso (e46.app (f04.obj P))]
    [IsIso (e67.app (f46.obj (f04.obj P)))]
    (hc : f37.map (oI.app P) ≫ oR.app (f02.obj P) ≫ f67.map (oA.app P) =
      oS.app (f01.obj P) ≫ f57.map (oP.app P) ≫ oB.app (f04.obj P)) :
    d37.map (lI.app (q0.obj P)) ≫ lR.app (d02.obj (q0.obj P)) ≫
      d67.map (lA.app (q0.obj P)) =
    lS.app (d01.obj (q0.obj P)) ≫ d57.map (lP.app (q0.obj P)) ≫
      lB.app (d04.obj (q0.obj P)) := by
  let ε := d67.map (d46.map (e04.app P)) ≫
    d67.map (e46.app (f04.obj P)) ≫ e67.app (f46.obj (f04.obj P))
  have : IsIso ε := by dsimp only [ε]; infer_instance
  apply (cancel_mono ε).1
  dsimp only [ε]
  simp only [Category.assoc]
  have hnR := lR.naturality (e02.app P)
  have hnB := lB.naturality (e04.app P)
  have heA := e67.naturality (oA.app P)
  have hrI := e37.naturality (oI.app P)
  have hbP := e57.naturality (oP.app P)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnR hnB heA hrI hbP
  have hAmap := congrArg d67.map hA
  have hImap := congrArg d37.map hI
  have hPmap := congrArg d57.map hP
  simp only [Functor.map_comp] at hAmap hImap hPmap
  have hL := paste_left hAmap heA hnR.symm hR hImap hrI
  have hRight := paste_right hnB.symm hB hPmap
    (lS.naturality (e01.app P)).symm hbP hS
  dsimp only [Functor.comp_map, Functor.comp_obj] at hRight
  refine Eq.trans hL (Eq.trans ?_ hRight.symm)
  slice_lhs 4 6 =>
    rw [← q7.map_comp, ← q7.map_comp, hc, q7.map_comp, q7.map_comp]

private theorem cochain_representative_cube
    {H0 D0 : Type*} [Category H0] [Preadditive H0] [Category D0]
    {H1 D1 : Type*} [Category H1] [Preadditive H1] [Category D1]
    {H2 D2 : Type*} [Category H2] [Preadditive H2] [Category D2]
    {H3 D3 : Type*} [Category H3] [Preadditive H3] [Category D3]
    {H4 D4 : Type*} [Category H4] [Preadditive H4] [Category D4]
    {H5 D5 : Type*} [Category H5] [Preadditive H5] [Category D5]
    {H6 D6 : Type*} [Category H6] [Preadditive H6] [Category D6]
    {H7 D7 : Type*} [Category H7] [Preadditive H7] [Category D7]
    (q0 : CochainComplex H0 ℤ ⥤ D0)
    (q1 : CochainComplex H1 ℤ ⥤ D1)
    (q2 : CochainComplex H2 ℤ ⥤ D2)
    (q3 : CochainComplex H3 ℤ ⥤ D3)
    (q4 : CochainComplex H4 ℤ ⥤ D4)
    (q5 : CochainComplex H5 ℤ ⥤ D5)
    (q6 : CochainComplex H6 ℤ ⥤ D6)
    (q7 : CochainComplex H7 ℤ ⥤ D7)
    (f01 : H0 ⥤ H1) [f01.Additive] (d01 : D0 ⥤ D1)
    (f02 : H0 ⥤ H2) [f02.Additive] (d02 : D0 ⥤ D2)
    (f04 : H0 ⥤ H4) [f04.Additive] (d04 : D0 ⥤ D4)
    (f13 : H1 ⥤ H3) [f13.Additive] (d13 : D1 ⥤ D3)
    (f15 : H1 ⥤ H5) [f15.Additive] (d15 : D1 ⥤ D5)
    (f23 : H2 ⥤ H3) [f23.Additive] (d23 : D2 ⥤ D3)
    (f26 : H2 ⥤ H6) [f26.Additive] (d26 : D2 ⥤ D6)
    (f37 : H3 ⥤ H7) [f37.Additive] (d37 : D3 ⥤ D7)
    (f45 : H4 ⥤ H5) [f45.Additive] (d45 : D4 ⥤ D5)
    (f46 : H4 ⥤ H6) [f46.Additive] (d46 : D4 ⥤ D6)
    (f57 : H5 ⥤ H7) [f57.Additive] (d57 : D5 ⥤ D7)
    (f67 : H6 ⥤ H7) [f67.Additive] (d67 : D6 ⥤ D7)
    (e01 : q0 ⋙ d01 ⟶ (f01.mapHomologicalComplex (.up ℤ)) ⋙ q1)
    (e02 : q0 ⋙ d02 ⟶ (f02.mapHomologicalComplex (.up ℤ)) ⋙ q2)
    (e04 : q0 ⋙ d04 ⟶ (f04.mapHomologicalComplex (.up ℤ)) ⋙ q4)
    (e13 : q1 ⋙ d13 ⟶ (f13.mapHomologicalComplex (.up ℤ)) ⋙ q3)
    (e15 : q1 ⋙ d15 ⟶ (f15.mapHomologicalComplex (.up ℤ)) ⋙ q5)
    (e23 : q2 ⋙ d23 ⟶ (f23.mapHomologicalComplex (.up ℤ)) ⋙ q3)
    (e26 : q2 ⋙ d26 ⟶ (f26.mapHomologicalComplex (.up ℤ)) ⋙ q6)
    (e37 : q3 ⋙ d37 ⟶ (f37.mapHomologicalComplex (.up ℤ)) ⋙ q7)
    (e45 : q4 ⋙ d45 ⟶ (f45.mapHomologicalComplex (.up ℤ)) ⋙ q5)
    (e46 : q4 ⋙ d46 ⟶ (f46.mapHomologicalComplex (.up ℤ)) ⋙ q6)
    (e57 : q5 ⋙ d57 ⟶ (f57.mapHomologicalComplex (.up ℤ)) ⋙ q7)
    (e67 : q6 ⋙ d67 ⟶ (f67.mapHomologicalComplex (.up ℤ)) ⋙ q7)
    (oI : f01 ⋙ f13 ⟶ f02 ⋙ f23)
    (lI : d01 ⋙ d13 ⟶ d02 ⋙ d23)
    (oR : f23 ⋙ f37 ⟶ f26 ⋙ f67)
    (lR : d23 ⋙ d37 ⟶ d26 ⋙ d67)
    (oP : f01 ⋙ f15 ⟶ f04 ⋙ f45)
    (lP : d01 ⋙ d15 ⟶ d04 ⋙ d45)
    (oB : f45 ⋙ f57 ⟶ f46 ⋙ f67)
    (lB : d45 ⋙ d57 ⟶ d46 ⋙ d67)
    (oA : f02 ⋙ f26 ⟶ f04 ⋙ f46)
    (lA : d02 ⋙ d26 ⟶ d04 ⋙ d46)
    (oS : f13 ⋙ f37 ⟶ f15 ⋙ f57)
    (lS : d13 ⋙ d37 ⟶ d15 ⋙ d57)
    (P : CochainComplex H0 ℤ)
    (hI : lI.app (q0.obj (P)) ≫ d23.map (e02.app (P)) ≫
      e23.app ((f02.mapHomologicalComplex (.up ℤ)).obj (P)) =
      d13.map (e01.app (P)) ≫ e13.app ((f01.mapHomologicalComplex (.up ℤ)).obj (P)) ≫
        q3.map ((NatTrans.mapHomologicalComplex oI (.up ℤ)).app (P)))
    (hR : lR.app (q2.obj ((f02.mapHomologicalComplex (.up ℤ)).obj P)) ≫ d67.map (e26.app
      ((f02.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      e67.app ((f26.mapHomologicalComplex (.up ℤ)).obj ((f02.mapHomologicalComplex (.up ℤ)).obj P))
      =
      d37.map (e23.app ((f02.mapHomologicalComplex (.up ℤ)).obj P)) ≫ e37.app
      ((f23.mapHomologicalComplex (.up ℤ)).obj ((f02.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        q7.map ((NatTrans.mapHomologicalComplex oR (.up ℤ)).app ((f02.mapHomologicalComplex (.up
      ℤ)).obj P)))
    (hP : lP.app (q0.obj (P)) ≫ d45.map (e04.app (P)) ≫
      e45.app ((f04.mapHomologicalComplex (.up ℤ)).obj (P)) =
      d15.map (e01.app (P)) ≫ e15.app ((f01.mapHomologicalComplex (.up ℤ)).obj (P)) ≫
        q5.map ((NatTrans.mapHomologicalComplex oP (.up ℤ)).app (P)))
    (hB : lB.app (q4.obj ((f04.mapHomologicalComplex (.up ℤ)).obj P)) ≫ d67.map (e46.app
      ((f04.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      e67.app ((f46.mapHomologicalComplex (.up ℤ)).obj ((f04.mapHomologicalComplex (.up ℤ)).obj P))
      =
      d57.map (e45.app ((f04.mapHomologicalComplex (.up ℤ)).obj P)) ≫ e57.app
      ((f45.mapHomologicalComplex (.up ℤ)).obj ((f04.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        q7.map ((NatTrans.mapHomologicalComplex oB (.up ℤ)).app ((f04.mapHomologicalComplex (.up
      ℤ)).obj P)))
    (hA : lA.app (q0.obj (P)) ≫ d46.map (e04.app (P)) ≫
      e46.app ((f04.mapHomologicalComplex (.up ℤ)).obj (P)) =
      d26.map (e02.app (P)) ≫ e26.app ((f02.mapHomologicalComplex (.up ℤ)).obj (P)) ≫
        q6.map ((NatTrans.mapHomologicalComplex oA (.up ℤ)).app (P)))
    (hS : lS.app (q1.obj ((f01.mapHomologicalComplex (.up ℤ)).obj P)) ≫ d57.map (e15.app
      ((f01.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      e57.app ((f15.mapHomologicalComplex (.up ℤ)).obj ((f01.mapHomologicalComplex (.up ℤ)).obj P))
      =
      d37.map (e13.app ((f01.mapHomologicalComplex (.up ℤ)).obj P)) ≫ e37.app
      ((f13.mapHomologicalComplex (.up ℤ)).obj ((f01.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        q7.map ((NatTrans.mapHomologicalComplex oS (.up ℤ)).app ((f01.mapHomologicalComplex (.up
      ℤ)).obj P)))
    [IsIso (e04.app P)] [IsIso (e46.app ((f04.mapHomologicalComplex (.up ℤ)).obj P))]
    [IsIso (e67.app ((f46.mapHomologicalComplex (.up ℤ)).obj ((f04.mapHomologicalComplex (.up
      ℤ)).obj P)))]
    (hc : (f37.mapHomologicalComplex (.up ℤ)).map ((NatTrans.mapHomologicalComplex oI (.up ℤ)).app
      P) ≫ (NatTrans.mapHomologicalComplex oR (.up ℤ)).app ((f02.mapHomologicalComplex (.up ℤ)).obj
      P) ≫ (f67.mapHomologicalComplex (.up ℤ)).map ((NatTrans.mapHomologicalComplex oA (.up ℤ)).app
      P) =
      (NatTrans.mapHomologicalComplex oS (.up ℤ)).app ((f01.mapHomologicalComplex (.up ℤ)).obj P) ≫
      (f57.mapHomologicalComplex (.up ℤ)).map ((NatTrans.mapHomologicalComplex oP (.up ℤ)).app P) ≫
      (NatTrans.mapHomologicalComplex oB (.up ℤ)).app ((f04.mapHomologicalComplex (.up ℤ)).obj P)) :
    d37.map (lI.app (q0.obj P)) ≫ lR.app (d02.obj (q0.obj P)) ≫
      d67.map (lA.app (q0.obj P)) =
    lS.app (d01.obj (q0.obj P)) ≫ d57.map (lP.app (q0.obj P)) ≫
      lB.app (d04.obj (q0.obj P)) := by
  exact representative_cube
    q0
    q1
    q2
    q3
    q4
    q5
    q6
    q7
    (f01.mapHomologicalComplex (.up ℤ)) d01
    (f02.mapHomologicalComplex (.up ℤ)) d02
    (f04.mapHomologicalComplex (.up ℤ)) d04
    (f13.mapHomologicalComplex (.up ℤ)) d13
    (f15.mapHomologicalComplex (.up ℤ)) d15
    (f23.mapHomologicalComplex (.up ℤ)) d23
    (f26.mapHomologicalComplex (.up ℤ)) d26
    (f37.mapHomologicalComplex (.up ℤ)) d37
    (f45.mapHomologicalComplex (.up ℤ)) d45
    (f46.mapHomologicalComplex (.up ℤ)) d46
    (f57.mapHomologicalComplex (.up ℤ)) d57
    (f67.mapHomologicalComplex (.up ℤ)) d67
    e01
    e02
    e04
    e13
    e15
    e23
    e26
    e37
    e45
    e46
    e57
    e67
    (NatTrans.mapHomologicalComplex oI (.up ℤ)) lI
    (NatTrans.mapHomologicalComplex oR (.up ℤ)) lR
    (NatTrans.mapHomologicalComplex oP (.up ℤ)) lP
    (NatTrans.mapHomologicalComplex oB (.up ℤ)) lB
    (NatTrans.mapHomologicalComplex oA (.up ℤ)) lA
    (NatTrans.mapHomologicalComplex oS (.up ℤ)) lS
    P hI hR hP hB hA hS hc


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
private theorem derived_cube {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} {s : Square.{u}} {a : Operations s A} {b : Operations s B}
    (c : Scalars s φ a b) (K : s.Z.derived A) :
    b.r.left.functor.map (c.atI.derived.hom.app K) ≫
        c.atR.derived.hom.app (a.i.left.functor.obj K) ≫
        (s.V.scalar φ).map (a.square.hom.app K) =
      b.square.hom.app ((s.Z.scalar φ).obj K) ≫
        b.b.left.functor.map (c.atP.derived.hom.app K) ≫
        c.atB.derived.hom.app (a.p.left.functor.obj K) := by
  let l : s.Z.scalar φ ⋙ b.i.left.functor ⋙ b.r.left.functor ⟶
      a.p.left.functor ⋙ a.b.left.functor ⋙ s.V.scalar φ :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight c.atI.derived.hom _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ c.atR.derived.hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight a.square.hom _ ≫
      (Functor.associator _ _ _).hom
  let r : s.Z.scalar φ ⋙ b.i.left.functor ⋙ b.r.left.functor ⟶
      a.p.left.functor ⋙ a.b.left.functor ⋙ s.V.scalar φ :=
    Functor.whiskerLeft _ b.square.hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight c.atP.derived.hom _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ c.atB.derived.hom
  suffices l = r by
    have h := congrArg (fun z ↦ z.app K) this
    simpa only [l, r, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc] using h
  let := HasDerivedCategory.standard (Mod (s.Z.ring A))
  apply resolving_nat_ext (M := Mod (s.Z.ring A)) (H := s.V.derived B)
    (fun P : Cx (s.Z.ring A) ↦ P.IsAcyclicTensorKFlat ∧
      ∀ n : ℤ, SheafOfModules.IsFlat (J := s.Z.J) (P.X n))
    (module_flat_kFlat_resolution (J := s.Z.J)) l r
  intro P hP
  let Pi := ((s.i.modules A).mapHomologicalComplex (.up ℤ)).obj P
  let Pp := ((s.p.modules A).mapHomologicalComplex (.up ℤ)).obj P
  let Pb := ((s.b.modules A).mapHomologicalComplex (.up ℤ)).obj Pp
  let Ps := ((change (s.Z.scalarMap φ)).mapHomologicalComplex (.up ℤ)).obj P
  have hi := pull_flat_kFlat s.i.algebra s.i.direct s.i.adj
    (constantMap s.i.algebra A) P hP.1 hP.2
  have hp := pull_flat_kFlat s.p.algebra s.p.direct s.p.adj
    (constantMap s.p.algebra A) P hP.1 hP.2
  have hb := pull_flat_kFlat s.b.algebra s.b.direct s.b.adj
    (constantMap s.b.algebra A) Pp hp.1 hp.2
  have hs := change_flat_kFlat (s.Z.scalarMap φ) P hP.1 hP.2
  have := a.p.exactComparison
  have := a.b.exactComparison
  have : IsIso (a.p.left.comparison.app P) := inferInstance
  have : IsIso (a.b.left.comparison.app Pp) := inferInstance
  have : IsIso ((extendComparison (s.V.scalarMap φ)).app Pb) := by
    unfold extendComparison
    exact (derivedExtension (s.V.scalarMap φ)).computation Pb hb.1
  have hc :
      ((s.r.modules B).mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex c.atI.ordinary (.up ℤ)).hom.app P) ≫
        (NatIso.mapHomologicalComplex c.atR.ordinary (.up ℤ)).hom.app Pi ≫
        ((change (s.V.scalarMap φ)).mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex a.ordinarySquare (.up ℤ)).hom.app P) =
      (NatIso.mapHomologicalComplex b.ordinarySquare (.up ℤ)).hom.app Ps ≫
        ((s.b.modules B).mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex c.atP.ordinary (.up ℤ)).hom.app P) ≫
        (NatIso.mapHomologicalComplex c.atB.ordinary (.up ℤ)).hom.app Pp := by
    apply HomologicalComplex.hom_ext
    intro n
    exact ordinary_cube c (P.X n)
  dsimp only [l, r, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.id_comp, Category.comp_id]
  refine cochain_representative_cube
    (Q (s.Z.ring A))
    (Q (s.Z.ring B))
    (Q (s.Y.ring A))
    (Q (s.Y.ring B))
    (Q (s.T.ring A))
    (Q (s.T.ring B))
    (Q (s.V.ring A))
    (Q (s.V.ring B))
    (change (s.Z.scalarMap φ)) (s.Z.scalar φ)
    (s.i.modules A) (a.i.left.functor)
    (s.p.modules A) (a.p.left.functor)
    (s.i.modules B) (b.i.left.functor)
    (s.p.modules B) (b.p.left.functor)
    (change (s.Y.scalarMap φ)) (s.Y.scalar φ)
    (s.r.modules A) (a.r.left.functor)
    (s.r.modules B) (b.r.left.functor)
    (change (s.T.scalarMap φ)) (s.T.scalar φ)
    (s.b.modules A) (a.b.left.functor)
    (s.b.modules B) (b.b.left.functor)
    (change (s.V.scalarMap φ)) (s.V.scalar φ)
    (extendComparison (s.Z.scalarMap φ))
    (a.i.left.comparison)
    (a.p.left.comparison)
    (b.i.left.comparison)
    (b.p.left.comparison)
    (extendComparison (s.Y.scalarMap φ))
    (a.r.left.comparison)
    (b.r.left.comparison)
    (extendComparison (s.T.scalarMap φ))
    (a.b.left.comparison)
    (b.b.left.comparison)
    (extendComparison (s.V.scalarMap φ))
    c.atI.ordinary.hom c.atI.derived.hom
    c.atR.ordinary.hom c.atR.derived.hom
    c.atP.ordinary.hom c.atP.derived.hom
    c.atB.ordinary.hom c.atB.derived.hom
    a.ordinarySquare.hom a.square.hom
    b.ordinarySquare.hom b.square.hom
    P ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact c.atI.resolving P hP.1 hP.2
  · exact c.atR.resolving Pi hi.1 hi.2
  · exact c.atP.resolving P hP.1 hP.2
  · exact c.atB.resolving Pp hp.1 hp.2
  · exact a.resolving P hP.1 hP.2
  · exact b.resolving Ps hs.1 hs.2
  · exact hc


attribute [local irreducible] ConstantCompletion.extend ConstantCompletion.pull

@[reassoc]
private theorem exchange_transpose {s : Square.{u}} {R : Type u} [CommRing R]
    (o : Operations s R) (N : s.T.derived R) :
    o.r.left.functor.map (o.exchange.app N) ≫ o.r.adj.counit.app _ =
      o.square.hom.app (o.p.right.obj N) ≫ o.b.left.functor.map (o.p.adj.counit.app N) :=
  mateEquiv_counit o.p.adj o.r.adj (TwoSquare.mk _ _ _ _ o.square.hom) N

@[reassoc]
private theorem chi_transpose {X W : Presentation.{u}} {v : Geometric X W}
    {A B : Type u} [CommRing A] [CommRing B] {φ : A →+* B}
    {a : Image v A} {b : Image v B} (c : ScalarComparison v φ a b)
    (N : X.derived A) :
    b.left.functor.map (c.chi.app N) ≫ b.adj.counit.app _ =
      c.derived.hom.app (a.right.obj N) ≫ (X.scalar φ).map (a.adj.counit.app N) :=
  mateEquiv_counit a.adj b.adj (TwoSquare.mk _ _ _ _ c.derived.hom) N

private theorem exchange_compatibility {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} {s : Square.{u}} {a : Operations s A} {b : Operations s B}
    (c : Scalars s φ a b)
    (cube : ∀ K : s.Z.derived A,
      b.r.left.functor.map (c.atI.derived.hom.app K) ≫
        c.atR.derived.hom.app (a.i.left.functor.obj K) ≫
        (s.V.scalar φ).map (a.square.hom.app K) =
      b.square.hom.app ((s.Z.scalar φ).obj K) ≫
        b.b.left.functor.map (c.atP.derived.hom.app K) ≫
        c.atB.derived.hom.app (a.p.left.functor.obj K))
    (N : s.T.derived A) :
    c.atI.derived.hom.app (a.p.right.obj N) ≫
        (s.Y.scalar φ).map (a.exchange.app N) ≫
        c.atR.chi.app (a.b.left.functor.obj N) =
      b.i.left.functor.map (c.atP.chi.app N) ≫
        b.exchange.app ((s.T.scalar φ).obj N) ≫
        b.r.right.map (c.atB.derived.hom.app N) := by
  apply (b.r.adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [chi_transpose]
  have hr := c.atR.derived.hom.naturality (a.exchange.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hr
  slice_lhs 2 3 => rw [hr]
  simp only [Category.assoc]
  rw [← (s.V.scalar φ).map_comp, exchange_transpose, Functor.map_comp]
  have hc := b.r.adj.counit.naturality (c.atB.derived.hom.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hc
  erw [hc, exchange_transpose_assoc]
  have hs := b.square.hom.naturality (c.atP.chi.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hs
  slice_rhs 1 2 => erw [hs]
  simp only [Category.assoc]
  slice_rhs 2 3 => rw [← b.b.left.functor.map_comp, chi_transpose, Functor.map_comp]
  have hb := c.atB.derived.hom.naturality (a.p.adj.counit.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hb
  simp only [Category.assoc]
  rw [hb]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ (s.V.scalar φ).map (a.b.left.functor.map (a.p.adj.counit.app N)))
    (cube (a.p.right.obj N))

private theorem open_unit_equation
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {IA : C ⥤ D} {LA : D ⥤ C} {IB : E ⥤ F} {LB : F ⥤ E}
    (a : IA ⊣ LA) (b : IB ⊣ LB) {S : C ⥤ E} {T : D ⥤ F}
    (β : IA ⋙ T ≅ S ⋙ IB) (lam : T ⋙ LB ≅ LA ⋙ S)
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ β.inv)).natTrans = lam.inv) (M : C) :
    b.unit.app (S.obj M) ≫ LB.map (β.inv.app M) ≫ lam.hom.app (IA.obj M) =
      S.map (a.unit.app M) := by
  have hm := unit_mateEquiv a b (TwoSquare.mk _ _ _ _ β.inv) M
  change S.map (a.unit.app M) ≫
    ((mateEquiv a b (TwoSquare.mk _ _ _ _ β.inv)).natTrans.app (IA.obj M)) = _ at hm
  rw [h] at hm
  change S.map (a.unit.app M) ≫ lam.inv.app (IA.obj M) =
    b.unit.app (S.obj M) ≫ LB.map (β.inv.app M) at hm
  rw [← Category.assoc, ← hm, Category.assoc, lam.inv_hom_id_app]
  exact Category.comp_id _

private theorem open_inverse_unit_equation
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {IA : C ⥤ D} {LA : D ⥤ C} {IB : E ⥤ F} {LB : F ⥤ E}
    (a : IA ⊣ LA) (b : IB ⊣ LB) [IsIso a.unit] [IsIso b.unit]
    {S : C ⥤ E} {T : D ⥤ F}
    (β : IA ⋙ T ≅ S ⋙ IB) (lam : T ⋙ LB ≅ LA ⋙ S)
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ β.inv)).natTrans = lam.inv) (M : C) :
    LB.map (β.hom.app M) ≫ inv (b.unit.app (S.obj M)) =
      lam.hom.app (IA.obj M) ≫ S.map (inv (a.unit.app M)) := by
  apply (cancel_epi (LB.map (β.inv.app M))).1
  apply (cancel_epi (b.unit.app (S.obj M))).1
  simp only [Functor.comp_obj, ← Category.assoc, ← LB.map_comp, β.inv_hom_id_app,
    LB.map_id, Category.comp_id, IsIso.hom_inv_id]
  slice_rhs 1 3 => exact open_unit_equation a b β lam h M
  rw [← S.map_comp, IsIso.hom_inv_id, S.map_id]
  rfl


private theorem gamma_normalization {s : Square.{u}} {R : Type u} [CommRing R]
    (o : Operations s R) (M : s.V.derived R) [IsIso (o.t M)] :
    o.openAdjI.unit.app (o.r.right.obj M) ≫
      o.i.left.functor.map (o.gamma M) ≫ o.t M = 𝟙 _ := by
  have h := (o.openAdjI.homEquiv _ _).apply_symm_apply (inv (o.t M))
  rw [Adjunction.homEquiv_unit] at h
  change o.openAdjI.unit.app _ ≫ o.i.left.functor.map (o.gamma M) = _ at h
  rw [← Category.assoc, h, IsIso.inv_hom_id]

private theorem t_compatibility {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} {s : Square.{u}} {a : Operations s A} {b : Operations s B}
    (c : Scalars s φ a b)
    (hex : ∀ N : s.T.derived A,
      c.atI.derived.hom.app (a.p.right.obj N) ≫
          (s.Y.scalar φ).map (a.exchange.app N) ≫
          c.atR.chi.app (a.b.left.functor.obj N) =
        b.i.left.functor.map (c.atP.chi.app N) ≫
          b.exchange.app ((s.T.scalar φ).obj N) ≫
          b.r.right.map (c.atB.derived.hom.app N))
    (M : s.V.derived A) :
    b.i.left.functor.map (c.atP.chi.app (a.extendB.obj M) ≫
        b.p.right.map (c.betaB.hom.app M)) ≫ b.t ((s.V.scalar φ).obj M) =
      c.atI.derived.hom.app (a.p.right.obj (a.extendB.obj M)) ≫
        (s.Y.scalar φ).map (a.t M) ≫ c.atR.chi.app M := by
  have hn := b.exchange.naturality (c.betaB.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  dsimp only [Operations.t]
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 2 3 => rw [hn]
  simp only [Category.assoc]
  rw [← b.r.right.map_comp,
    open_inverse_unit_equation a.openAdjB b.openAdjB c.betaB c.atB.derived c.betaB_mate M,
    b.r.right.map_comp]
  slice_lhs 1 3 => rw [← hex]
  simp only [Category.assoc]
  have hc := c.atR.chi.naturality (inv (a.openAdjB.unit.app M))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hc
  rw [hc]

private theorem gamma_compatibility {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} {s : Square.{u}} {a : Operations s A} {b : Operations s B}
    (c : Scalars s φ a b)
    (ht : ∀ M : s.V.derived A,
      b.i.left.functor.map (c.atP.chi.app (a.extendB.obj M) ≫
          b.p.right.map (c.betaB.hom.app M)) ≫ b.t ((s.V.scalar φ).obj M) =
        c.atI.derived.hom.app (a.p.right.obj (a.extendB.obj M)) ≫
          (s.Y.scalar φ).map (a.t M) ≫ c.atR.chi.app M)
    (M : s.V.derived A) [IsIso (a.t M)] [IsIso (b.t ((s.V.scalar φ).obj M))] :
    (s.Z.scalar φ).map (a.gamma M) ≫ c.atP.chi.app (a.extendB.obj M) ≫
        b.p.right.map (c.betaB.hom.app M) =
      c.betaI.hom.app (a.r.right.obj M) ≫
        b.extendI.map (c.atR.chi.app M) ≫ b.gamma ((s.V.scalar φ).obj M) := by
  apply (cancel_epi (c.betaI.inv.app (a.r.right.obj M))).1
  simp only [← Category.assoc, c.betaI.inv_hom_id_app, Category.id_comp]
  apply (b.openAdjI.homEquiv _ _).injective
  rw [b.openAdjI.homEquiv_naturality_left]
  dsimp only [Functor.comp_obj]
  rw [show b.openAdjI.homEquiv _ _ (b.gamma ((s.V.scalar φ).obj M)) =
    inv (b.t ((s.V.scalar φ).obj M)) from
      (b.openAdjI.homEquiv _ _).apply_symm_apply _]
  apply (cancel_mono (b.t ((s.V.scalar φ).obj M))).1
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id]
  slice_lhs 4 5 => rw [← b.i.left.functor.map_comp]
  rw [ht M]
  have hn := c.atI.derived.hom.naturality (a.gamma M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  slice_lhs 3 4 => rw [hn]
  simp only [Category.assoc]
  slice_lhs 1 3 =>
    exact open_unit_equation a.openAdjI b.openAdjI c.betaI c.atI.derived c.betaI_mate _
  rw [← (s.Y.scalar φ).map_comp, ← (s.Y.scalar φ).map_comp,
    Category.assoc, gamma_normalization, Functor.map_id]
  exact Category.id_comp _

private theorem t_naturality {s : Square.{u}} {R : Type u} [CommRing R]
    (o : Operations s R) {M N : s.V.derived R} (f : M ⟶ N) :
    o.i.left.functor.map (o.p.right.map (o.extendB.map f)) ≫ o.t N =
      o.t M ≫ o.r.right.map f := by
  have hn := o.exchange.naturality (o.extendB.map f)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  have hu := o.openAdjB.unit.naturality f
  change f ≫ o.openAdjB.unit.app N =
    o.openAdjB.unit.app M ≫ o.b.left.functor.map (o.extendB.map f) at hu
  have hi : o.b.left.functor.map (o.extendB.map f) ≫ inv (o.openAdjB.unit.app N) =
      inv (o.openAdjB.unit.app M) ≫ f := by
    apply (cancel_epi (o.openAdjB.unit.app M)).1
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rw [← hu, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  dsimp only [Operations.t]
  rw [← Category.assoc, hn, Category.assoc, ← o.r.right.map_comp, hi,
    o.r.right.map_comp, Category.assoc]

private theorem gamma_naturality {s : Square.{u}} {R : Type u} [CommRing R]
    (o : Operations s R) (M N : s.V.derived R)
    [IsIso (o.t M)] [IsIso (o.t N)] (f : M ⟶ N) :
    o.extendI.map (o.r.right.map f) ≫ o.gamma N =
      o.gamma M ≫ o.p.right.map (o.extendB.map f) := by
  apply o.openAdjI.homEquiv_naturality_right_square
  apply (cancel_mono (o.t N)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [t_naturality, IsIso.inv_hom_id_assoc]


/-- Scalar compatibility of exchange and of its normalized inverse-exchange adjunct.
Source: main-20261015, sk-thm-purity-transport.proof.md, Steps 1 and 3;
Stacks 07A4, 0D6D, 07A7, 0GL1
(blueprint: lem-pur-topos-scalar-inverse-exchange-mate).

Proof:
1. Before deriving, both scalar/inverse-image pastings pull the coefficient and module
   through the same geometric square and then balance. The pure equations of the four
   scalar comparisons and the two coefficient squares identify these maps on generators.
   The sheafified tensor hom equivalence determines equality from these insertions.
2. Check the derived cube on flat-term K-flat resolutions. Postcompose both routes
   with the invertible pullback and scalar computation maps. The resolving equations
   and naturality reduce the result to the ordinary cube applied degreewise. Pullback
   and scalar extension preserve this resolving class. Localization extensionality
   then proves the inverse-image scalar cube on all unbounded objects.
3. Transpose the first identity under r_B. The counit-transpose identity for the actual
   mates chi and exchange rewrites both sides as the two pastings of that cube. Thus
   the transposes, and hence the morphisms, agree. Neither chi is inverted.
4. Apply the unit formula for mates to the supplied beta mate equations to obtain
   the inverse-open-unit equation for b and i. At N = I_b M, combine the first identity,
   naturality of exchange, and naturality of chi_r for the inverse b-unit. This gives
   t_B L_i(q) = chi_r S_Y(t_A) lambda_i, where q = chi_p followed by R_p(beta_b).
5. Precompose the second identity with beta_i inverse and transpose under I_iB.
   One transpose is t_B inverse followed by chi_r. After composing the other with t_B,
   step 4, naturality of lambda_i, and the open unit equation reduce it to chi_r,
   because gamma_A is the adjunct of t_A inverse. Cancel only t_B. The adjunction
   bijection gives the original equality of B-linear morphisms.
6. The defining transpose gives the normalization of gamma. Its naturality follows
   from naturality of exchange and the units, and inversion of the natural t square
   on the full subcategory of invertible inputs. Restriction to D+ preserves all these
   equalities whenever every displayed object and scalar extension lies in D+.
No properness, finite-ring, Noetherianity or scalar flatness enters the argument. -/
theorem scalar_inverse_exchange_mate
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (s : Square.{u}) (a : Operations s A) (b : Operations s B)
    (c : Scalars s φ a b) :
    (∀ N : s.T.derived A,
      c.atI.derived.hom.app (a.p.right.obj N) ≫
          (s.Y.scalar φ).map (a.exchange.app N) ≫
          c.atR.chi.app (a.b.left.functor.obj N) =
        b.i.left.functor.map (c.atP.chi.app N) ≫
          b.exchange.app ((s.T.scalar φ).obj N) ≫
          b.r.right.map (c.atB.derived.hom.app N)) ∧
    (∀ (M : s.V.derived A) [IsIso (a.t M)] [IsIso (b.t ((s.V.scalar φ).obj M))],
      (s.Z.scalar φ).map (a.gamma M) ≫ c.atP.chi.app (a.extendB.obj M) ≫
          b.p.right.map (c.betaB.hom.app M) =
        c.betaI.hom.app (a.r.right.obj M) ≫
          b.extendI.map (c.atR.chi.app M) ≫ b.gamma ((s.V.scalar φ).obj M)) ∧
    (∀ (M : s.V.derived A) [IsIso (a.t M)],
      a.openAdjI.unit.app (a.r.right.obj M) ≫
          a.i.left.functor.map (a.gamma M) ≫ a.t M = 𝟙 _) ∧
    (∀ (M : s.V.derived B) [IsIso (b.t M)],
      b.openAdjI.unit.app (b.r.right.obj M) ≫
          b.i.left.functor.map (b.gamma M) ≫ b.t M = 𝟙 _) ∧
    (∀ (M N : s.V.derived A) [IsIso (a.t M)] [IsIso (a.t N)] (f : M ⟶ N),
      a.extendI.map (a.r.right.map f) ≫ a.gamma N =
        a.gamma M ≫ a.p.right.map (a.extendB.map f)) ∧
    (∀ (M N : s.V.derived B) [IsIso (b.t M)] [IsIso (b.t N)] (f : M ⟶ N),
      b.extendI.map (b.r.right.map f) ≫ b.gamma N =
        b.gamma M ≫ b.p.right.map (b.extendB.map f)) := by
  have hex := exchange_compatibility (φ := φ) (s := s) (a := a) (b := b) c
    (fun K ↦ derived_cube (φ := φ) (s := s) (a := a) (b := b) c K)
  refine ⟨hex, ?_, ?_, ?_, ?_, ?_⟩
  · intro M ha hb
    exact gamma_compatibility c (fun K ↦ t_compatibility c hex K) M
  · intro M hM
    exact gamma_normalization a M
  · intro M hM
    exact gamma_normalization b M
  · intro M N hM hN f
    exact gamma_naturality a M N f
  · intro M N hM hN f
    exact gamma_naturality b M N f

end CategoryTheory.ToposScalarInverseExchange
