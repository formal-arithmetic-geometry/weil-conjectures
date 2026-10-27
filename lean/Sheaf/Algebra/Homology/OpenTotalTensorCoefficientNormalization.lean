module

public import Sheaf.Algebra.Homology.OpenTotalTensorCoefficientData

/-! # Strict coefficient interchange for open total tensor

Source: Stacks Project, Modules on Sites, Tag 0E8I, and Cohomology on Sites,
Tag 0GL1; agent coefficient refinement
(blueprint: def-sf-open-total-tensor-coefficient-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


attribute [local irreducible] SheafOfModules.monoidalCategory

universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.LocalizedStrictTensor
namespace SheafOfModules.OpenTotalTensorCoefficient

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- Generator normalization of the ordinary comparison and its inverse.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-normalization). -/
structure GammaNormalization (e : Comparisons.{c, v, r} R V) : Prop where
  gamma_forward : ∀ (B : Sheaf J CommRingCat.{max c v r})
    (Q : Complex.{max c v, v, r} (B.over V)) (F : Complex.{c, v, r} B)
    (p q n : ℤ) (h : p + q = n) (W : C) (f : W ⟶ V)
    (x : (Q.X p).val.obj (op (Over.mk f))) (y : (F.X q).val.obj (op W)),
    ((e.gamma B Q F).hom.f n).val.app (op W)
      (totalSection.{c, v, r} B _ F p q n h (op W)
        (extensionSection.{c, v, r} B V (Q.X p) W f x) y) =
      extensionSection.{c, v, r} B V _ W f
        (totalSection.{max c v, v, r} (B.over V) Q _ p q n h (op (Over.mk f)) x y)
  gamma_inverse : ∀ (B : Sheaf J CommRingCat.{max c v r})
    (Q : Complex.{max c v, v, r} (B.over V)) (F : Complex.{c, v, r} B)
    (p q n : ℤ) (h : p + q = n) (W : C) (f : W ⟶ V)
    (x : (Q.X p).val.obj (op (Over.mk f))) (y : (F.X q).val.obj (op W)),
    ((e.gamma B Q F).inv.f n).val.app (op W)
      (extensionSection.{c, v, r} B V _ W f
        (totalSection.{max c v, v, r} (B.over V) Q _ p q n h (op (Over.mk f)) x y)) =
      totalSection.{c, v, r} B _ F p q n h (op W)
        (extensionSection.{c, v, r} B V (Q.X p) W f x) y

/-- Generator normalization of the ordinary comparison and its inverse.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-normalization). -/
structure LinearNormalization (e : Comparisons.{c, v, r} R V) : Prop where
  linear_normalized : ∀ (A : Under R) (Q : Complex.{max c v, v, r} (R.over V))
    (n : ℤ) (W : C) (f : W ⟶ V)
    (x : (Q.X n).val.obj (op (Over.mk f))) (a : A.right.obj.obj (op W)),
    ((e.linear A Q).hom.f n).val.app (op W)
      (CategoryTheory.CochainPullback.extensionTmul.{max c v r, c, v}
        A.hom (((extension.{c, v, r} R V).obj Q).X n)
        (op W) a
        (extensionSection.{c, v, r} R V (Q.X n) W f x)) =
      extensionSection.{c, v, r} A.right V _ W f
        (CategoryTheory.CochainPullback.extensionTmul.{max c v r, max c v, v}
          (slice.{c, v, r} R V A).hom (Q.X n) (op (Over.mk f)) a x)

  linear_inverse : ∀ (A : Under R) (Q : Complex.{max c v, v, r} (R.over V))
    (n : ℤ) (W : C) (f : W ⟶ V)
    (x : (Q.X n).val.obj (op (Over.mk f))) (a : A.right.obj.obj (op W)),
    ((e.linear A Q).inv.f n).val.app (op W)
      (extensionSection.{c, v, r} A.right V _ W f
        (CategoryTheory.CochainPullback.extensionTmul.{max c v r, max c v, v}
          (slice.{c, v, r} R V A).hom (Q.X n) (op (Over.mk f)) a x)) =
      CategoryTheory.CochainPullback.extensionTmul.{max c v r, c, v}
        A.hom (((extension.{c, v, r} R V).obj Q).X n) (op W) a
        (extensionSection.{c, v, r} R V (Q.X n) W f x)

/-- Restriction commutes with scalar extension by the identity on tensor sections.
Source: Stacks 03EL (blueprint: def-sf-open-total-tensor-coefficient-normalization). -/
structure RestrictionNormalization (e : Comparisons.{c, v, r} R V) : Prop where
  normalized : ∀ (A : Under R) (F : Complex.{c, v, r} R) (n : ℤ)
    (W : C) (f : W ⟶ V) (x : (F.X n).val.obj (op W))
    (a : A.right.obj.obj (op W)),
    (((e.restrictionCoefficient A F).hom.f n).val.app (op (Over.mk f)))
      (CategoryTheory.CochainPullback.extensionTmul.{max c v r, max c v, v}
        (slice.{c, v, r} R V A).hom _ (op (Over.mk f)) a x) =
      CategoryTheory.CochainPullback.extensionTmul.{max c v r, c, v}
        A.hom (F.X n) (op W) a x

/-- The left composite γ_n b_n^X, in the category of A-linear complexes.
Source: Stacks 0E8I, coefficient refinement
(blueprint: def-sf-open-total-tensor-coefficient-normalization). -/
def Comparisons.left (e : Comparisons.{c, v, r} R V) (A : Under R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R) :
    source.{c, v, r} R V A Q F ≅ target.{c, v, r} R V A Q F :=
  e.baseBalanced R V A Q F ≪≫
    (tensorRight ((change.{c, v, r} A.hom).obj F)).mapIso (e.linear A Q) ≪≫
    e.gamma A.right _ _

/-- The right composite j_!(b_n^V) r_(G_V,n) (γ^B tensor 1).
Source: Stacks 0E8I, coefficient refinement
(blueprint: def-sf-open-total-tensor-coefficient-normalization). -/
def Comparisons.right (e : Comparisons.{c, v, r} R V) (A : Under R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R) :
    source.{c, v, r} R V A Q F ≅ target.{c, v, r} R V A Q F :=
  (change.{c, v, r} A.hom).mapIso (e.gamma R Q F) ≪≫
    e.linear A (sliceTotal.{c, v, r} R V Q F) ≪≫
    (extension.{c, v, r} A.right V).mapIso (e.sliceBalanced R V A Q F)

/-- A strict coefficient diagram, after actual restriction of scalars to R.
The indexing category is all unital R-algebra sheaves, so its functor laws retain
identities, composites, arbitrary quotient transitions and maps between towers.
Source: Stacks 03EK and the agent strict coefficient refinement of 0E8I
(blueprint: def-sf-open-total-tensor-coefficient-normalization). -/
structure StrictFamily (X : ∀ A : Under R, Complex.{c, v, r} A.right) where
  map : ∀ {A B : Under R}, (a : A ⟶ B) →
    ((forget.{c, v, r} A.hom).obj (X A) ⟶ (forget.{c, v, r} B.hom).obj (X B))
  map_id : ∀ A, map (𝟙 A) = 𝟙 _
  map_comp : ∀ {A B D : Under R} (a : A ⟶ B) (b : B ⟶ D),
    map (a ≫ b) = map a ≫ map b

/-- Package the supplied strict diagram laws as the ordinary functor.
Source: Stacks Categories, strict diagrams
(blueprint: def-sf-open-total-tensor-coefficient-normalization). -/
def StrictFamily.functor {X : ∀ A : Under R, Complex.{c, v, r} A.right}
    (D : StrictFamily.{c, v, r} R X) : Under R ⥤ Complex.{c, v, r} R where
  obj A := (forget.{c, v, r} A.hom).obj (X A)
  map a := D.map a
  map_id := D.map_id
  map_comp := D.map_comp

/-- Naturality of scalar-linear isomorphisms after scalar restriction.
This includes inverse transition squares, since its components are isomorphisms.
Source: Stacks 03EK, strict coefficient refinement of 0E8I
(blueprint: def-sf-open-total-tensor-coefficient-normalization). -/
def IsStrict {X Y : ∀ A : Under R, Complex.{c, v, r} A.right}
    (D : StrictFamily.{c, v, r} R X) (E : StrictFamily.{c, v, r} R Y)
    (e : ∀ A, X A ≅ Y A) : Prop :=
  ∀ {A B : Under R} (a : A ⟶ B),
    D.map a ≫ (forget.{c, v, r} B.hom).map (e B).hom =
      (forget.{c, v, r} A.hom).map (e A).hom ≫ E.map a

/-- The actual isomorphism of strict coefficient diagrams.
Source: Stacks 03EK, strict coefficient refinement of 0E8I
(blueprint: def-sf-open-total-tensor-coefficient-normalization). -/
def strictIso {X Y : ∀ A : Under R, Complex.{c, v, r} A.right}
    (D : StrictFamily.{c, v, r} R X) (E : StrictFamily.{c, v, r} R Y)
    (e : ∀ A, X A ≅ Y A) (h : IsStrict.{c, v, r} R D E e) :
    D.functor R ≅ E.functor R :=
  NatIso.ofComponents (fun A ↦ (forget.{c, v, r} A.hom).mapIso (e A)) h

/-- Transpose strict towers of complexes into complexes of strict towers.
The localization below is therefore in the category of systems itself.
Source: Stacks 0941 (blueprint: def-sf-open-total-tensor-coefficient-normalization). -/
def transpose : (ℕᵒᵖ ⥤ Complex.{c, v, r} R) ⥤
    CochainComplex (ℕᵒᵖ ⥤ Modules.{c, v, r} R) ℤ where
  obj T :=
    { X := fun i ↦ T ⋙ HomologicalComplex.eval _ _ i
      d := fun i k ↦
        { app := fun n ↦ (T.obj n).d i k
          naturality := fun _ _ f ↦ (T.map f).comm i k }
      shape := fun i k h ↦ NatTrans.ext (funext (fun n ↦ (T.obj n).shape i k h))
      d_comp_d' := fun i k m _ _ ↦ NatTrans.ext (funext (fun n ↦
        (T.obj n).d_comp_d i k m)) }
  map f :=
    { f := fun i ↦
        { app := fun n ↦ (f.app n).f i
          naturality := fun _ _ g ↦ congrArg (fun a ↦ a.f i) (f.naturality g) }
      comm' := fun i k _ ↦ NatTrans.ext (funext (fun n ↦ (f.app n).comm i k)) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The standard derived localization of complexes of strict module towers.
Source: Stacks 05RU (blueprint: def-sf-open-total-tensor-coefficient-normalization). -/
def localizeTower :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Modules.{c, v, r} R)
  DerivedCategory.Q (C := ℕᵒᵖ ⥤ Modules.{c, v, r} R)

/-- The canonical source map on two chain maps.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-normalization). -/
def sourceMap (A : Under R)
    {Q Q' : Complex.{max c v, v, r} (R.over V)} {F F' : Complex.{c, v, r} R}
    (u : Q ⟶ Q') (v : F ⟶ F') :
    source.{c, v, r} R V A Q F ⟶ source.{c, v, r} R V A Q' F' :=
  (change.{c, v, r} A.hom).map
    (((extension.{c, v, r} R V).map u ⊗ₘ v))

/-- The canonical target map on two chain maps.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-normalization). -/
def targetMap (A : Under R)
    {Q Q' : Complex.{max c v, v, r} (R.over V)} {F F' : Complex.{c, v, r} R}
    (u : Q ⟶ Q') (v : F ⟶ F') :
    target.{c, v, r} R V A Q F ⟶ target.{c, v, r} R V A Q' F' :=
  (extension.{c, v, r} A.right V).map
    (((change.{max c v, v, r} (slice.{c, v, r} R V A).hom).map u) ⊗ₘ
      ((restriction.{c, v, r} A.right V).map ((change.{c, v, r} A.hom).map v)))


end SheafOfModules.OpenTotalTensorCoefficient
