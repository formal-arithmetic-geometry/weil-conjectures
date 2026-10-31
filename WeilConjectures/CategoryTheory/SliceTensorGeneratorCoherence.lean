/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SliceTensorGeneratorInterfaces
import WeilConjectures.CategoryTheory.SliceNormalizedScalarComparisons
import WeilConjectures.CategoryTheory.SliceNormalizedTensorTransport
import WeilConjectures.CategoryTheory.SliceTensorTowerAssembly

/-! # Generator-normalized slice tensor coefficient coherence

Source: Stacks Project, Modules on Sites, Tags 03DI, 03CY and 0E8I;
the agent's generator and strict-coherence refinement
(blueprint: lem-sf-cbc-slice-tensor-generator-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.LocalizedStrictTensor

namespace SheafOfModules.SliceTensorGenerator

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]


variable (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- All comparisons and their strict coefficient coherence, with the stated generators.
The restriction comparison is oriented opposite to κ, so κ is its inverse. The
scalar-linear comparison is an isomorphism in S-modules, using multiplication
on the scalar factor of the actual scalar extension. The ordinary comparison
is an isomorphism of strict towers, natural in the module and coefficient tower.
Source: Stacks 03DI, 03CY and 0E8I, agent generator refinement
(blueprint: lem-sf-cbc-slice-tensor-generator-coherence). -/
structure Coherence where
  /-- Identity on the extension-presheaf summands after scalar restriction. -/
  restrictionComparison : ∀ A : Under R,
    scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj A) ⋙
        localizedSystemExtension.{c, v, r} R V ≅
      localizedSystemExtension.{c, v, r} A.right V ⋙ scalars.{c, v, r} R A
  /-- Its action is specified on genuine sheafification generators. -/
  restriction_normalized : ∀ A,
    ScalarExtensionNormalized.{c, v, r} R V A (restrictionComparison A)
  /-- Those generators uniquely determine the scalar-restriction comparison. -/
  restriction_unique : ∀ A e,
    ScalarExtensionNormalized.{c, v, r} R V A e → e = restrictionComparison A
  /-- The underlying R-tensor carries the actual scalar-extension action. -/
  tensorLift : ∀ A : Under R, TensorLift.{c, v, r} R A
  /-- The transport uses precisely the ordinary tensor sheafification generators. -/
  tensorLift_normalized : ∀ A, TensorLiftNormalized.{c, v, r} R A (tensorLift A)
  /-- The same transport on the localized site. -/
  sliceTensorLift : ∀ A : Under R,
    TensorLift.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj A)
  /-- The localized transport is fixed by the same pure-tensor formula. -/
  sliceTensorLift_normalized : ∀ A,
    TensorLiftNormalized.{max c v, v, r} (R.over V)
      ((sliceAlgebras.{c, v, r} R V).obj A) (sliceTensorLift A)
  /-- The comparison is S-linear and natural in the slice module. -/
  linear : ∀ A : Under R, LinearComparison.{c, v, r} R V A
  /-- Forward formula: [m] tensor s maps to [m tensor s]. -/
  linear_normalized : ∀ A, LinearNormalized.{c, v, r} R V A (linear A)
  /-- Its inverse is induced by the reverse formula on actual generators. -/
  linear_inverse : ∀ (A : Under R) (M : Modules.{max c v, v, r} (R.over V))
    (W : C) (a : W ⟶ V) (m : M.val.obj (op (Over.mk a)))
    (s : A.right.obj.obj (op W)),
    ((linear A).inv.app M).val.app (op W)
      (extensionSection.{c, v, r} A.right V _ W a
        (scalarExtensionSection.{max c v, v, max c v r, max c v r}
          ((sliceAlgebras.{c, v, r} R V).obj A).hom M (op (Over.mk a)) s m)) =
      scalarExtensionSection.{c, v, max c v r, max c v r} A.hom _ (op W) s
        (extensionSection.{c, v, r} R V M W a m)
  /-- Uniqueness makes this the canonical normalized scalar-linear comparison. -/
  linear_unique : ∀ A e, LinearNormalized.{c, v, r} R V A e → e = linear A
  /-- The strict tower comparison, natural in every slice-module map. -/
  ordinary : ∀ S : AlgebraTowers.{c, v, r} R,
    localizedSystemExtension.{c, v, r} R V ⋙ reduction.{c, v, r} R S ≅
      reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        towerExtension.{c, v, r} R V
  /-- Normalization in every degree-zero module and every tower level. -/
  ordinary_normalized : ∀ S, OrdinaryNormalized.{c, v, r} R V S (ordinary S)
  /-- The generator formula determines the ordinary comparison uniquely. -/
  ordinary_unique : ∀ S e,
    OrdinaryNormalized.{c, v, r} R V S e → e = ordinary S
  /-- Every level has the stated S-linear lift, through κ and the tensor transports. -/
  ordinary_linear : ∀ (S : AlgebraTowers.{c, v, r} R)
    (M : Modules.{max c v, v, r} (R.over V)) (n : ℕᵒᵖ),
    ((ordinary S).hom.app M).app n =
      (tensorLift (S.obj n)).hom.app ((localizedSystemExtension.{c, v, r} R V).obj M) ≫
        (scalars.{c, v, r} R (S.obj n)).map ((linear (S.obj n)).hom.app M) ≫
        (restrictionComparison (S.obj n)).inv.app
          ((extend.{max c v, v, r} ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)).hom).obj M) ≫
        (localizedSystemExtension.{c, v, r} R V).map
          ((sliceTensorLift (S.obj n)).inv.app M)
  /-- Inserting the scalar unit is intertwined on the actual extension generators. -/
  unit_normalized : ∀ (S : AlgebraTowers.{c, v, r} R)
    (M : Modules.{max c v, v, r} (R.over V)) (n : ℕᵒᵖ)
    (W : C) (a : W ⟶ V) (p : M.val.obj (op (Over.mk a))),
    (((ordinary S).hom.app M).app n).val.app (op W)
      (SheafOfModules.LocalizedStrictTensor.pure.{c, v, r} R _ _ (op W)
        (extensionSection.{c, v, r} R V M W a p) (1 : (S.obj n).right.obj.obj (op W))) =
      extensionSection.{c, v, r} R V _ W a
        (SheafOfModules.LocalizedStrictTensor.pure.{max c v, v, r} (R.over V) _ _
          (op (Over.mk a)) p (1 : (S.obj n).right.obj.obj (op W)))
  /-- Algebra-tower maps commute strictly with the comparison, before localization. -/
  coefficient_natural : ∀ (S T : AlgebraTowers.{c, v, r} R) (a : S ⟶ T),
    Functor.whiskerLeft (localizedSystemExtension.{c, v, r} R V)
        ((reductionFamily.{c, v, r} R).map a) ≫ (ordinary T).hom =
      (ordinary S).hom ≫
        Functor.whiskerRight
          ((reductionFamily.{max c v, v, r} (R.over V)).map
            (Functor.whiskerRight a (sliceAlgebras.{c, v, r} R V)))
          (towerExtension.{c, v, r} R V)

/-- Apply exactly the normalized comparison degreewise to any unbounded complex.
Its type is an isomorphism of complexes of strict towers. Thus both differential
commutation and every tower-transition square are literal equations of maps;
naturality in chain maps is included in this natural isomorphism.
Source: Stacks 0E8I, agent strict-chain refinement
(blueprint: lem-sf-cbc-slice-tensor-generator-coherence). -/
def Coherence.onComplexes (e : Coherence.{c, v, r} R V)
    (S : AlgebraTowers.{c, v, r} R) :=
  comparisonOnComplexes.{c, v, r} R V S (e.ordinary S)

/-- Generator-normalized slice tensor comparisons exist, with coefficient-linear
lifts and strict coherence for every unbounded complex and every algebra tower.
Source: Stacks 03DI, 03CY and 0E8I, agent refinement of the generator formulas
(blueprint: lem-sf-cbc-slice-tensor-generator-coherence).

Proof:
1. Module sheafification has the associated abelian and set sheafifications
   (lem-pc-sites-module-sheafification-interface and
   lem-pc-sites-sheafification-underlying-sets). Its unit is locally surjective
   by lem-cbc-presheaf-sheafification-epi-local-lifts. Thus finite sums of original
   extension summands, and locally pure tensor sections, test equality of sheaf maps.
2. The two extension presheaves after restriction of scalars have the same summands,
   restrictions and actions (def-weil-extension-by-zero-presheaf and
   def-pc-sheaf-restrict-scalars). Sheafification and uniqueness of its extended action
   give the identity-on-generators comparison κ and its naturality.
3. Apply lem-sf-ringed-slice-tensor-generators to M and the restricted scalar algebra.
   Identify the ordinary tensor with scalar extension followed by restriction using
   their identical sectionwise balanced tensors and the sheafification universal
   property. Compose with κ inverse to obtain the displayed forward and reverse maps.
4. On a generator multiplication by q sends [m] tensor s to [m] tensor qs; both
   formulas preserve that action. Local generation gives S-linearity and uniqueness.
5. Module maps act on m and algebra maps act on s, so both naturality composites have
   the prescribed identical value. The local generator test makes these map equations.
6. In degree i the tensor differential is d tensor 1, since S is in degree zero
   (def-pc-tensor-complex-sheaves). Both chain composites send [p] tensor s to
   [d(p) tensor s], for arbitrary unbounded complexes. The inverse chain equation follows
   by composing with the inverse components.
7. For every adjacent transition s_n both tower composites send [p] tensor t to
   [p tensor s_n(t)]. The inverse components satisfy the same square; longer transitions
   follow by composition (def-weil-inverse-system).
8. For a tower map a both composites send [p] tensor s to [p tensor a_n(s)]. For s=1,
   unitality gives [p tensor 1], so the scalar-unit maps are intertwined. None of these
   arguments uses flatness, boundedness, surjectivity or localization. -/
theorem coherence_exists : Nonempty (Coherence.{c, v, r} R V) := by
  classical
  obtain ⟨k, l, hk, hku, hl, hlu⟩ := scalarComparisons_exists.{c, v, r} R V
  obtain ⟨t, ht⟩ := tensorTransport_exists.{c, v, r} R
  obtain ⟨ts, hts⟩ := tensorTransport_exists.{max c v, v, r} (R.over V)
  let tv := fun A : Under R ↦ ts ((sliceAlgebras.{c, v, r} R V).obj A)
  have htv : ∀ A, TensorLiftNormalized.{max c v, v, r} (R.over V)
      ((sliceAlgebras.{c, v, r} R V).obj A) (tv A) :=
    fun A ↦ hts ((sliceAlgebras.{c, v, r} R V).obj A)
  obtain ⟨o, ho, hou, hol, hoc⟩ :=
    tensorTowerAssembly_exists.{c, v, r} R V k t tv l hk ht htv hl
  refine ⟨{
    restrictionComparison := k
    restriction_normalized := hk
    restriction_unique := hku
    tensorLift := t
    tensorLift_normalized := ht
    sliceTensorLift := tv
    sliceTensorLift_normalized := htv
    linear := l
    linear_normalized := hl
    linear_inverse := ?_
    linear_unique := hlu
    ordinary := o
    ordinary_normalized := ho
    ordinary_unique := hou
    ordinary_linear := hol
    unit_normalized := fun S M n W a p ↦ ho S M n W a p 1
    coefficient_natural := hoc
  }⟩
  intro A M W a m s
  have h := congrArg (fun x ↦ ((l A).inv.app M).val.app (op W) x)
    (hl A M W a m s)
  refine h.symm.trans ?_
  exact congrArg (fun f ↦ f.val.app (op W)
    (scalarExtensionSection.{c, v, max c v r, max c v r} A.hom _ (op W) s
      (extensionSection.{c, v, r} R V M W a m))) ((l A).app M).hom_inv_id

end SheafOfModules.SliceTensorGenerator
