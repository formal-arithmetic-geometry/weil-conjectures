module

public import Sheaf.Algebra.Homology.OpenTotalTensorCoefficientCoherence
import Sheaf.Algebra.Homology.OpenTotalTensorNormalizedComparisons
import Sheaf.Algebra.Homology.OpenTotalTensorGeneratorCalculus
import Sheaf.Algebra.Homology.OpenTotalTensorSourceFamily

/-! # Strict coefficient interchange for open total tensor

Source: Stacks Project, Modules on Sites, Tag 0E8I, and Cohomology on Sites,
Tag 0GL1; agent coefficient refinement
(blueprint: lem-sf-open-total-tensor-coefficient-interchange).
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

private theorem pure_hom_ext
    {D : Type c} [Category.{v} D] {K : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{max c v r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (B : Sheaf K CommRingCat.{max c v r}) (M N H : Modules.{c, v, r} B)
    (a b : M ⊗ N ⟶ H)
    (h : ∀ W x y, a.val.app W (LocalizedStrictTensor.pure.{c, v, r} B M N W x y) =
      b.val.app W (LocalizedStrictTensor.pure.{c, v, r} B M N W x y)) : a = b := by
  let e := tensorObjIsoSheafification (R := B) M N
  apply (cancel_epi e.inv).mp
  apply (PresheafOfModules.sheafificationAdjunction
    (R := LocalizedStrictTensor.ring.{c, v, r} B) (𝟙 _)).homEquiv _ _ |>.injective
  apply PresheafOfModules.hom_ext
  intro W
  ext t
  change a.val.app W (e.inv.val.app W
      (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (LocalizedStrictTensor.ring.{c, v, r} B).obj)).unit.app
        (M.val ⊗ N.val)).app W t)) =
    b.val.app W (e.inv.val.app W
      (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (LocalizedStrictTensor.ring.{c, v, r} B).obj)).unit.app
        (M.val ⊗ N.val)).app W t))
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => exact h W x y
  | add t u ht hu => simp only [map_add, ht, hu]

private theorem source_hom_ext
    (e : Comparisons.{c, v, r} R V) (hg : GammaNormalization.{c, v, r} R V e)
    (A : Under R) (Q : Complex.{max c v, v, r} (R.over V))
    (F : Complex.{c, v, r} R) (H : Complex.{c, v, r} A.right)
    (a b : source.{c, v, r} R V A Q F ⟶ H)
    (h : ∀ (p q n : ℤ) (hpq : p + q = n) (W : C) (f : W ⟶ V)
      (x : (Q.X p).val.obj (op (Over.mk f))) (y : (F.X q).val.obj (op W))
      (s : A.right.obj.obj (op W)),
      (a.f n).val.app (op W) (sourceSection.{c, v, r} R V A Q F p q n hpq W f x y s) =
        (b.f n).val.app (op W) (sourceSection.{c, v, r} R V A Q F p q n hpq W f x y s)) :
    a = b := by
  apply HomologicalComplex.Hom.ext
  funext n
  let adj := CategoryTheory.CochainPullback.extensionAdjunction A.hom
  apply adj.homEquiv _ (H.X n) |>.injective
  let g := (HomologicalComplex.eval _ _ n).mapIso (e.gamma R Q F)
  apply (cancel_epi g.inv).mp
  apply (localizedSystemAdjunction.{c, v, r} R V).homEquiv _ _ |>.injective
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply pure_hom_ext.{max c v, v, r} (R.over V) (Q.X p) ((F.X q).over V) _
  intro W x y
  have hu : ((localizedSystemAdjunction.{c, v, r} R V).unit.app
      ((sliceTotal.{c, v, r} R V Q F).X n)).val.app W
      (totalSection.{max c v, v, r} (R.over V) Q
              ((restriction.{c, v, r} R V).obj F) p q n hpq W x y) =
      extensionSection.{c, v, r} R V ((sliceTotal.{c, v, r} R V Q F).X n)
        W.unop.left W.unop.hom
        (totalSection.{max c v, v, r} (R.over V) Q
              ((restriction.{c, v, r} R V).obj F) p q n hpq W x y) :=
    (localizedSystemAdjunction_existsUnique.{c, v, r} R V).exists.choose_spec _ W _
  have hs : ∀ z : ((extendedTotal.{c, v, r} R V Q F).X n).val.obj (op W.unop.left),
      (adj.unit.app ((extendedTotal.{c, v, r} R V Q F).X n)).val.app (op W.unop.left) z =
        CategoryTheory.CochainPullback.extensionTmul A.hom _ (op W.unop.left) 1 z :=
    fun z ↦ (Classical.choose_spec
      (CategoryTheory.CochainPullback.extensionAdjunction_existsUnique A.hom)).1 _ _ z
  change (a.f n).val.app (op W.unop.left)
      ((adj.unit.app _).val.app (op W.unop.left)
        (((e.gamma R Q F).inv.f n).val.app (op W.unop.left)
          (((localizedSystemAdjunction.{c, v, r} R V).unit.app _).val.app W
            (totalSection.{max c v, v, r} (R.over V) Q
              ((restriction.{c, v, r} R V).obj F) p q n hpq W x y)))) =
    (b.f n).val.app (op W.unop.left)
      ((adj.unit.app _).val.app (op W.unop.left)
        (((e.gamma R Q F).inv.f n).val.app (op W.unop.left)
          (((localizedSystemAdjunction.{c, v, r} R V).unit.app _).val.app W
            (totalSection.{max c v, v, r} (R.over V) Q
              ((restriction.{c, v, r} R V).obj F) p q n hpq W x y))))
  erw [hu, hg.gamma_inverse, hs]
  exact h p q n hpq W.unop.left W.unop.hom x y 1

/-- Strict coefficient interchange exists for arbitrary unbounded complexes and
all unital coefficient algebras simultaneously, hence for every strict tower.
Source: Stacks Modules on Sites 0E8I, Cohomology on Sites 0GL1, agent refinement
(blueprint: lem-sf-open-total-tensor-coefficient-interchange).

Proof:
1. Totalize the normalized sheaf comparison from
   lem-sf-ringed-slice-tensor-generators using preservation of direct sums by
   lem-pur-site-restriction-module-adjunction-exact. Naturality in the two
   differentials preserves d(x tensor y)=dx tensor y+(-1)^p x tensor dy.
   lem-sf-ringed-open-total-tensor-kflat supplies the same total-tensor shape.
2. Use lem-sf-cbc-slice-tensor-generator-coherence for the coefficient-linear
   comparison r and its scalar-restriction identification. Specialize
   lem-pur-cochain-pullback-tensor-coherence to the identity topos for b^X,b^V;
   compose the slice version with lem-sfb-localized-site-tensor-restriction.
3. The left composite on ([x]_f tensor y) tensor a first distributes a and 1,
   then moves extension through coefficient change, then through tensor. Its
   value is [(x tensor a) tensor (y tensor 1)]_f. The right composite first moves
   extension through tensor, then through scalar change, then distributes a,1.
   It has exactly the same value.
4. Pure tensors determine balanced maps; the extension direct sum is determined
   on every f-summand; sheafification extends such maps uniquely. Total-degree
   maps are determined by all (p,q) insertions, also for unbounded complexes.
   These universal properties promote step 3 to the scalar-linear equation.
5. The inverse formulas reverse the two extension comparisons and multiply
   the two coefficient entries for the balanced comparison. All preserve (p,q).
   Chain identities include the same sign for negative p and imply the inverse
   chain identities by composing with the inverse maps.
6. A unital algebra map replaces both scalar entries and preserves their product
   and 1. The normalized formulas therefore define strict transition maps and
   give both naturality squares; identities and composites hold on generators.
   This gives every q_(m,n) square and inverse square before localization.
7. Chain maps replace x,y by their images, proving naturality in both complexes.
   Applying a functor from the tower index to the algebra category gives the
   asserted strict B-module towers and coefficient-tower naturality. Localization
   preserves this already strict equality. No flatness, boundedness, completeness
   or surjectivity assumption is used. -/
theorem interchange_exists :
    ∃ e : Comparisons.{c, v, r} R V,
      GammaNormalization.{c, v, r} R V e ∧ LinearNormalization.{c, v, r} R V e ∧
      RestrictionNormalization.{c, v, r} R V e ∧
      Nonempty (StrictCoherence.{c, v, r} R V e) := by
  classical
  obtain ⟨e, hg, hl, hr⟩ := normalizedComparisons_exists.{c, v, r} R V
  obtain ⟨hv, hw, hi, hn⟩ := normalized_composite_values.{c, v, r} R V e hg hl hr
  have heq : ∀ A Q F, (e.left R V A Q F).hom = (e.right R V A Q F).hom := by
    intro A Q F
    apply source_hom_ext.{c, v, r} R V e hg A Q F
    intro p q n h W f x y a
    exact (hv A Q F p q n h W f x y a).trans (hw A Q F p q n h W f x y a).symm
  have hex := sourceCoefficientFamily_exists.{c, v, r} R V
  choose D hD using hex
  let i := fun (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R)
    (A : Under R) ↦ (forget.{c, v, r} A.hom).mapIso (e.left R V A Q F)
  let E : ∀ Q F, StrictFamily.{c, v, r} R (fun A ↦ target.{c, v, r} R V A Q F) :=
    fun Q F ↦
      { map := fun {A B} a ↦ (i Q F A).inv ≫ (D Q F).map a ≫ (i Q F B).hom
        map_id := fun A ↦ by
          rw [(D Q F).map_id]
          exact (congrArg (fun f ↦ (i Q F A).inv ≫ f)
            (Category.id_comp (i Q F A).hom)).trans (i Q F A).inv_hom_id
        map_comp := fun a b ↦ by
          simp only [(D Q F).map_comp, Category.assoc, Iso.hom_inv_id_assoc] }
  have hstrict : ∀ Q F, IsStrict.{c, v, r} R (D Q F) (E Q F) (fun A ↦ e.left R V A Q F) := by
    intro Q F A B a
    change (D Q F).map a ≫ (i Q F B).hom =
      (i Q F A).hom ≫ (i Q F A).inv ≫ (D Q F).map a ≫ (i Q F B).hom
    simp only [Iso.hom_inv_id_assoc]
  have hrstrict : ∀ Q F,
      IsStrict.{c, v, r} R (D Q F) (E Q F) (fun A ↦ e.right R V A Q F) := by
    intro Q F A B a
    simpa only [← heq] using hstrict Q F a
  have htower : ∀ (S : AlgebraTowers.{c, v, r} R) Q F,
      Functor.whiskerLeft S
        (strictIso.{c, v, r} R (D Q F) (E Q F) (fun A ↦ e.left R V A Q F) (hstrict Q F)).hom =
      Functor.whiskerLeft S
        (strictIso.{c, v, r} R (D Q F) (E Q F) (fun A ↦ e.right R V A Q F) (hrstrict Q F)).hom := by
    intro S Q F
    apply NatTrans.ext
    funext n
    exact congrArg (forget.{c, v, r} (S.obj n).hom).map (heq (S.obj n) Q F)
  have hback : ∀ A Q F p q n h W f x y a b,
      (((e.left R V A Q F).hom.f n).val.app (op W))
        (sourceSection.{c, v, r} R V A Q F p q n h W f x y (a * b)) =
      targetSection.{c, v, r} R V A Q F p q n h W f x y a b := by
    intro A Q F p q n h W f x y a b
    rw [← hi A Q F p q n h W f x y a b]
    exact congrArg (fun k ↦ (k.f n).val.app (op W)
      (targetSection.{c, v, r} R V A Q F p q n h W f x y a b)) (e.left R V A Q F).inv_hom_id
  refine ⟨e, hg, hl, hr, ⟨{
    equation := heq
    generator := hv
    generator_inverse := hi
    sourceFamily := D
    targetFamily := E
    source_transition := fun a Q F ↦ hD Q F a
    target_transition := ?_
    left_strict := hstrict
    right_strict := hrstrict
    tower_equation := htower
    localized_equation := ?_
    natural := hn }⟩⟩
  · intro A B a Q F p q n h W f x y s t
    change (((e.left R V B Q F).hom.f n).val.app (op W))
      ((((D Q F).map a).f n).val.app (op W)
        ((((e.left R V A Q F).inv.f n).val.app (op W))
          (targetSection.{c, v, r} R V A Q F p q n h W f x y s t))) = _
    rw [hi, hD]
    have hm := (a.right.hom.app (op W)).hom.map_mul s t
    rw [hm]
    exact hback B Q F p q n h W f x y _ _
  · intro S Q F
    rw [htower]

end SheafOfModules.OpenTotalTensorCoefficient
