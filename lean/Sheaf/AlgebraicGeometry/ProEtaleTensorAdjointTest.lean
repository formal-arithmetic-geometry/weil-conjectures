/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.CategoryTheory.GeometricModuleConstruction
import Sheaf.CategoryTheory.GeometricModuleTransport

/-! # Adjoint tests for inverse images of tensor products

Source: Stacks Project, Modules on Sites, Tags 03D3, 03D7 and Section 03EK.
(blueprint: lem-pur-inverse-image-tensor-adjoint-test).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtaleTensorComparison
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Forget commutativity in the coefficient sheaf. Source: Stacks 03D3
(blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable abbrev proEtaleTestRing {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R

/-- The existing module category on the original site. Source: Stacks 03D3
(blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
abbrev proEtaleTestModules {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  CategoryTheory.ringedSiteModules.{u + 1, u + 1, u, u + 1} (proEtaleTestRing R)

/-- Forget the module structure to sets. Source: Stacks 03D3
(blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable abbrev proEtaleTestUnderlying {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  SheafOfModules.toSheaf (proEtaleTestRing R) ⋙
    sheafCompose (ProEt.topology T) (CategoryTheory.forget AddCommGrpCat.{u + 1})

/-- The recorded sheafified sectionwise tensor, at the original site universes.
Source: Stacks 03EK (blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable abbrev proEtaleTestTensor {T : Scheme.{u}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M N : proEtaleTestModules R) :=
  (SheafOfModules.siteSheafTensorRight N).obj M

/-- The sheafification image of a pure tensor. Source: Stacks 03EK
(blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable abbrev proEtaleTestPure {T : Scheme.{u}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M N : proEtaleTestModules R) (V : T.ProEtᵒᵖ)
    (s : M.val.obj V) (t : N.val.obj V) :=
  SheafOfModules.siteSheafTensorTmul M N V s t

/-- Direct image of modules with the action induced by the actual ring-adjunction unit.
Source: Stacks 03D3 (blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable def proEtaleTestDirectImage {T' T : Scheme.{u}} (h : T' ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange h)
    (J := ProEt.topology T) (K := ProEt.topology T')
    (S := proEtaleTestRing R)
    (R := proEtaleTestRing ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
    ⟨Functor.whiskerRight ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- The original-unit section, evaluated in the already specified small-model construction.
Source: Stacks 03D3 (blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable def proEtaleTestUnitSection {T' T : Scheme.{u}} (h : T' ⟶ T)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M : proEtaleTestModules R) (V : T.ProEtᵒᵖ) (s : M.val.obj V) :
    ((proEtaleModuleInverseImage h R).obj M).val.obj
      (op ((proEtaleBaseChange h).obj V.unop)) :=
  inverseSection h M V.unop s

/-- The specified unit sections assemble into a unique module morphism.
Source: Stacks 03D3 (blueprint: lem-pur-inverse-image-tensor-adjoint-test).
Proof: evaluate the small-model adjunction unit on every original site object.
Its components are linear through the ring unit. Its naturality equation, transported
back along AsSmall.up, is exactly the required module naturality. Sectionwise
extensionality proves uniqueness. This assembles existing data without choosing an action. -/
theorem proEtaleTestModuleUnit_exists {T' T : Scheme.{u}} (h : T' ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (M : proEtaleTestModules R) :
    ∃! η : M ⟶ (proEtaleTestDirectImage h R).obj
        ((proEtaleModuleInverseImage h R).obj M),
      ∀ (V : T.ProEtᵒᵖ) (s : M.val.obj V),
        η.val.app V s = proEtaleTestUnitSection h M V s := by
  sorry

/-- The unique module map with the actual adjunction-unit components.
Source: Stacks 03D3 (blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable def proEtaleTestModuleUnit {T' T : Scheme.{u}} (h : T' ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (M : proEtaleTestModules R) :
    M ⟶ (proEtaleTestDirectImage h R).obj ((proEtaleModuleInverseImage h R).obj M) :=
  Classical.choose (proEtaleTestModuleUnit_exists h R M)

/-- The module-valued expression `h_* α ∘ η`, using the specified constructions.
Source: Stacks 03D3 (blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
noncomputable def proEtaleTestAdjunct {T' T : Scheme.{u}} (h : T' ⟶ T)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {M : proEtaleTestModules R}
    {K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)}
    (α : (proEtaleModuleInverseImage h R).obj M ⟶ K) :
    M ⟶ (proEtaleTestDirectImage h R).obj K :=
  proEtaleTestModuleUnit h R M ≫ (proEtaleTestDirectImage h R).map α

/-- The Bilin set introduced in the statement: sectionwise R-bilinear maps commuting
with every restriction, equivalently morphisms from the product of the underlying sheaves.
Source: Stacks 03EK (blueprint: lem-pur-inverse-image-tensor-adjoint-test). -/
def proEtaleTestBilin {T : Scheme.{u}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M N H : proEtaleTestModules R) :=
  { β : ∀ V : T.ProEtᵒᵖ,
      M.val.obj V →ₗ[R.obj.obj V] N.val.obj V →ₗ[R.obj.obj V] H.val.obj V //
    ∀ {V W : T.ProEtᵒᵖ} (f : V ⟶ W) (s : M.val.obj V) (t : N.val.obj V),
      β W (M.val.map f s) (N.val.map f t) = H.val.map f (β V s t) }

/-- The adjoint bilinear test, with the specified set-sheaf adjunct and full naturality.
Source: Stacks 03D3, 03D7 and Section 03EK
(blueprint: lem-pur-inverse-image-tensor-adjoint-test).
Proof:
1. Identify the geometric-module functors with the specified inverse and direct images,
using their transported addition and scalar actions. The direct action is through η_R.
2. geometric_module_transport gives the module Hom bijection and identifies its
underlying map with h_*α composed with η. The forward linearity follows from linearity
of the unit and α; the inverse linearity follows from the transport theorem, without
any assertion about generation by original sections. Naturality gives the two formulas.
3. Compose this bijection with tensor_bilinear_universal on the original site (transport
to its small model if needed). A bilinear sheaf map is exactly a restriction-compatible
family of sectionwise curried linear maps. Its formula is evaluation on the original
unit pure tensors. This is a bijection and is natural in all three modules, since
(u tensor v)(s tensor t) = u(s) tensor v(t).
4. Injectivity of that bijection gives the equality test. The converse follows by
substitution. No generation of sections on arbitrary target-site objects is used. -/
theorem proEtale_inverseImage_tensor_adjoint_test {T' T : Scheme.{u}} (h : T' ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    (∀ (M N : proEtaleTestModules R)
      (K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)),
      Function.Bijective (fun α :
        (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K ↦
          proEtaleTestAdjunct h α)) ∧
    (∀ (M N M' N' : proEtaleTestModules R)
      (K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
      (a : M ⟶ M') (b : N ⟶ N')
      (α : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M' N') ⟶ K),
      proEtaleTestAdjunct h
          ((proEtaleModuleInverseImage h R).map (tensorMap a b) ≫ α) =
        tensorMap a b ≫ proEtaleTestAdjunct h α) ∧
    (∀ (M N : proEtaleTestModules R)
      (K K' : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
      (α : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K) (k : K ⟶ K'),
      proEtaleTestAdjunct h (α ≫ k) =
        proEtaleTestAdjunct h α ≫ (proEtaleTestDirectImage h R).map k) ∧
    (∀ (M N : proEtaleTestModules R)
      (K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
      (α : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K),
      (proEtaleTestUnderlying R).map (proEtaleTestAdjunct h α) =
        (proEtaleSheafAdjunction h (Type (u + 1))).homEquiv _ _
          ((moduleSetsIdentification h (proEtaleTestTensor M N)).hom ≫
            (proEtaleTestUnderlying
              ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)).map α)) ∧
    (∃ E : ∀ (M N : proEtaleTestModules R)
        (K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)),
        ((proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K) ≃
          proEtaleTestBilin M N ((proEtaleTestDirectImage h R).obj K),
      (∀ (M N : proEtaleTestModules R)
        (K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
        (α : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K)
        (V : T.ProEtᵒᵖ) (s : M.val.obj V) (t : N.val.obj V),
        (E M N K α).val V s t = α.val.app (op ((proEtaleBaseChange h).obj V.unop))
          (proEtaleTestUnitSection h (proEtaleTestTensor M N) V
            (proEtaleTestPure M N V s t))) ∧
      (∀ (M N M' N' : proEtaleTestModules R)
        (K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
        (a : M ⟶ M') (b : N ⟶ N')
        (α : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M' N') ⟶ K)
        (V : T.ProEtᵒᵖ) (s : M.val.obj V) (t : N.val.obj V),
        (E M N K ((proEtaleModuleInverseImage h R).map (tensorMap a b) ≫ α)).val V s t =
          (E M' N' K α).val V (a.val.app V s) (b.val.app V t)) ∧
      (∀ (M N : proEtaleTestModules R)
        (K K' : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
        (α : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K) (k : K ⟶ K')
        (V : T.ProEtᵒᵖ) (s : M.val.obj V) (t : N.val.obj V),
        (E M N K' (α ≫ k)).val V s t =
          k.val.app (op ((proEtaleBaseChange h).obj V.unop)) ((E M N K α).val V s t))) ∧
    (∀ (M N : proEtaleTestModules R)
      (K : proEtaleTestModules ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
      (α β : (proEtaleModuleInverseImage h R).obj (proEtaleTestTensor M N) ⟶ K),
      α = β ↔ ∀ (V : T.ProEtᵒᵖ) (s : M.val.obj V) (t : N.val.obj V),
        α.val.app (op ((proEtaleBaseChange h).obj V.unop))
            (proEtaleTestUnitSection h (proEtaleTestTensor M N) V
              (proEtaleTestPure M N V s t)) =
          β.val.app (op ((proEtaleBaseChange h).obj V.unop))
            (proEtaleTestUnitSection h (proEtaleTestTensor M N) V
              (proEtaleTestPure M N V s t))) := by
  sorry


/-- Coefficient-change evaluations for supplied normalized maps. The quotient and scalar
identifications are the existing uniquely characterized canonical maps, not supplied
arbitrary arrows. Source: Stacks 03EK, and original parent proof step 4
(blueprint: lem-pur-inverse-image-tensor-adjoint-test).
Proof: naturality of the unit with the coefficient quotient sends the original unit
pure tensor to the larger-ring pure tensor. The scalar identification preserves unit
sections. Applying the supplied larger-ring b gives the displayed target value. On
the other route the supplied smaller-ring b first gives the smaller-ring pure tensor;
tensorMap of the scalar identifications and then the canonical quotient give precisely
the same larger-ring pure tensor. Only the two supplied normalization equations are used. -/
theorem proEtale_inverseImage_tensor_coefficient_evaluations
    {T' T : Scheme.{u}} (h : T' ⟶ T)
    (b : ∀ (S : Rings T) (P Q : Modules S),
      (inverse h S).obj (tensor P Q) ⟶ tensor ((inverse h S).obj P) ((inverse h S).obj Q))
    (hb : ∀ (S : Rings T) (P Q : Modules S) (V : T.ProEt)
      (s : P.val.obj (op V)) (t : Q.val.obj (op V)),
      (b S P Q).val.app (op ((proEtaleBaseChange h).obj V))
          (inverseSection h (tensor P Q) V (pure P Q V s t)) =
        pure ((inverse h S).obj P) ((inverse h S).obj Q) ((proEtaleBaseChange h).obj V)
          (inverseSection h P V s) (inverseSection h Q V t))
    {R S : Rings T} (φ : R ⟶ S) (M N : Modules S)
    (V : T.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V)) :
    (((inverse h R).map (coefficientQuotient φ M N) ≫
        (scalarIdentification h φ (tensor M N)).hom ≫
        (restrict (inverseRingMap h φ)).map (b S M N)).val.app
          (op ((proEtaleBaseChange h).obj V))
            (inverseSection h (tensor ((restrict φ).obj M) ((restrict φ).obj N)) V
              (pure ((restrict φ).obj M) ((restrict φ).obj N) V s t)) =
      pure ((inverse h S).obj M) ((inverse h S).obj N) ((proEtaleBaseChange h).obj V)
        (inverseSection h M V s) (inverseSection h N V t)) ∧
    ((b R ((restrict φ).obj M) ((restrict φ).obj N) ≫
        tensorMap (scalarIdentification h φ M).hom (scalarIdentification h φ N).hom ≫
        coefficientQuotient (inverseRingMap h φ)
          ((inverse h S).obj M) ((inverse h S).obj N)).val.app
          (op ((proEtaleBaseChange h).obj V))
            (inverseSection h (tensor ((restrict φ).obj M) ((restrict φ).obj N)) V
              (pure ((restrict φ).obj M) ((restrict φ).obj N) V s t)) =
      pure ((inverse h S).obj M) ((inverse h S).obj N) ((proEtaleBaseChange h).obj V)
        (inverseSection h M V s) (inverseSection h N V t)) := by
  sorry

/-- Composition evaluations for a supplied algebraic, unit-normalized set compositor.
The ring isomorphism c and module components d express exactly compatibility with the
transported operations: their underlying set maps are the supplied δ components. The
unit equation uses the canonical fibre-product associator via lowerStarComp. No
existence assertion for δ, b_h, b_g or b_hg is made.
Source: Stacks 03D2 and 03EK, and original parent proof step 7
(blueprint: lem-pur-inverse-image-tensor-adjoint-test).
Proof:
1. The supplied unit equation for δ sends the composite unit image of s tensor t to
its iterated unit image, after restriction along the canonical associator. Its
algebraic compatibility gives exactly the same formula for d on modules.
2. Naturality of the g-unit with b_h sends that iterated image to the g-unit of
h-inverse(s) tensor h-inverse(t). These are sections on the original object h^*V
of the intermediate site, so the assumed normalization of b_g applies. The result
is the tensor of the two iterated unit images, restricted along the associator.
3. On the other route b_hg first gives the composite unit images of s and t. The
tensor map of d followed by the coefficient quotient sends them to the tensor of
their d-images. The supplied unit equation identifies these with the same iterated
unit images. Restriction commutes with the pure pairing. This proves both evaluated
equalities without assuming naturality or invertibility of any supplied b. -/
theorem proEtale_inverseImage_tensor_composition_evaluations
    {T'' T' T : Scheme.{u}} (g : T'' ⟶ T') (h : T' ⟶ T)
    (R : Rings T)
    (δ : AlgebraicGeometry.ProEtale.setPullback (g ≫ h) ≅
      AlgebraicGeometry.ProEtale.setPullback h ⋙ AlgebraicGeometry.ProEtale.setPullback g)
    (hδ : ∀ H : Sheaf (ProEt.topology T) (Type (u + 1)),
      (AlgebraicGeometry.ProEtale.setPullbackAdjunction (g ≫ h)).unit.app H ≫
          (AlgebraicGeometry.ProEtale.lowerStar (Type (u + 1)) (g ≫ h)).map (δ.hom.app H) =
        ((AlgebraicGeometry.ProEtale.setPullbackAdjunction h).comp
          (AlgebraicGeometry.ProEtale.setPullbackAdjunction g)).unit.app H ≫
          (AlgebraicGeometry.ProEtale.lowerStarComp (Type (u + 1)) g h).hom.app
            ((AlgebraicGeometry.ProEtale.setPullback h ⋙
              AlgebraicGeometry.ProEtale.setPullback g).obj H))
    (c : inverseRing (g ≫ h) R ≅ inverseRing g (inverseRing h R))
    (hc : (ringSetsIdentification (g ≫ h) R).hom ≫ ringMapSets c.hom =
      δ.hom.app (ringSets R) ≫
        (AlgebraicGeometry.ProEtale.setPullback g).map (ringSetsIdentification h R).hom ≫
        (ringSetsIdentification g (inverseRing h R)).hom)
    (d : ∀ P : Modules R, (inverse (g ≫ h) R).obj P ≅
      (restrict c.hom).obj ((inverse g (inverseRing h R)).obj ((inverse h R).obj P)))
    (hd : ∀ P : Modules R,
      (moduleSetsIdentification (g ≫ h) P).hom ≫ moduleMapSets (d P).hom =
        δ.hom.app (moduleSets P) ≫
          (AlgebraicGeometry.ProEtale.setPullback g).map (moduleSetsIdentification h P).hom ≫
          (moduleSetsIdentification g ((inverse h R).obj P)).hom)
    (bh : ∀ (S : Rings T) (P Q : Modules S), (inverse h S).obj (tensor P Q) ⟶
      tensor ((inverse h S).obj P) ((inverse h S).obj Q))
    (bg : ∀ (S : Rings T') (P Q : Modules S), (inverse g S).obj (tensor P Q) ⟶
      tensor ((inverse g S).obj P) ((inverse g S).obj Q))
    (bc : ∀ (S : Rings T) (P Q : Modules S), (inverse (g ≫ h) S).obj (tensor P Q) ⟶
      tensor ((inverse (g ≫ h) S).obj P) ((inverse (g ≫ h) S).obj Q))
    (hbh : ∀ (S : Rings T) (P Q : Modules S) (V : T.ProEt)
      (s : P.val.obj (op V)) (t : Q.val.obj (op V)),
      (bh S P Q).val.app (op ((proEtaleBaseChange h).obj V))
          (inverseSection h (tensor P Q) V (pure P Q V s t)) =
        pure ((inverse h S).obj P) ((inverse h S).obj Q) ((proEtaleBaseChange h).obj V)
          (inverseSection h P V s) (inverseSection h Q V t))
    (hbg : ∀ (S : Rings T') (P Q : Modules S) (V : T'.ProEt)
      (s : P.val.obj (op V)) (t : Q.val.obj (op V)),
      (bg S P Q).val.app (op ((proEtaleBaseChange g).obj V))
          (inverseSection g (tensor P Q) V (pure P Q V s t)) =
        pure ((inverse g S).obj P) ((inverse g S).obj Q)
          ((proEtaleBaseChange g).obj V) (inverseSection g P V s) (inverseSection g Q V t))
    (hbc : ∀ (S : Rings T) (P Q : Modules S) (V : T.ProEt)
      (s : P.val.obj (op V)) (t : Q.val.obj (op V)),
      (bc S P Q).val.app (op ((proEtaleBaseChange (g ≫ h)).obj V))
          (inverseSection (g ≫ h) (tensor P Q) V (pure P Q V s t)) =
        pure ((inverse (g ≫ h) S).obj P) ((inverse (g ≫ h) S).obj Q)
          ((proEtaleBaseChange (g ≫ h)).obj V)
          (inverseSection (g ≫ h) P V s) (inverseSection (g ≫ h) Q V t))
    (M N : Modules R) (V : T.ProEt) (s : M.val.obj (op V)) (t : N.val.obj (op V)) :
    (((d (tensor M N)).hom ≫
        (restrict c.hom).map ((inverse g (inverseRing h R)).map (bh R M N)) ≫
        (restrict c.hom).map
          (bg (inverseRing h R) ((inverse h R).obj M) ((inverse h R).obj N))).val.app
          (op ((proEtaleBaseChange (g ≫ h)).obj V))
            (inverseSection (g ≫ h) (tensor M N) V (pure M N V s t)) =
      (tensor ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))).val.map
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app V).op
          (pure ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
            ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))
            ((proEtaleBaseChange g).obj ((proEtaleBaseChange h).obj V))
            (inverseSection g ((inverse h R).obj M) ((proEtaleBaseChange h).obj V)
              (inverseSection h M V s))
            (inverseSection g ((inverse h R).obj N) ((proEtaleBaseChange h).obj V)
              (inverseSection h N V t)))) ∧
    ((bc R M N ≫ tensorMap (d M).hom (d N).hom ≫ coefficientQuotient c.hom
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))).val.app
          (op ((proEtaleBaseChange (g ≫ h)).obj V))
            (inverseSection (g ≫ h) (tensor M N) V (pure M N V s t)) =
      (tensor ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
        ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))).val.map
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app V).op
          (pure ((inverse g (inverseRing h R)).obj ((inverse h R).obj M))
            ((inverse g (inverseRing h R)).obj ((inverse h R).obj N))
            ((proEtaleBaseChange g).obj ((proEtaleBaseChange h).obj V))
            (inverseSection g ((inverse h R).obj M) ((proEtaleBaseChange h).obj V)
              (inverseSection h M V s))
            (inverseSection g ((inverse h R).obj N) ((proEtaleBaseChange h).obj V)
              (inverseSection h N V t)))) := by
  sorry

end AlgebraicGeometry.ProEtaleTensorComparison
