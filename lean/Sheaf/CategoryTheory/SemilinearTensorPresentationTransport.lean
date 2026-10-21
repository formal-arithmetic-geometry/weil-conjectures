/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.CategoryTheory.SemilinearTensorPresentationData
import Sheaf.CategoryTheory.GeometricModuleTransport
import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
import Sheaf.Paper.RingedTopoiInverseImageTensorComparison
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

/-! # Semilinear tensor transport through a ring presentation

Source: the integral-twist paragraph of
literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-prop-sfb-cartesian-coefficients-twists.proof.md; Stacks Tags 03CY, 03D1--03D3, 03EK, 03EL.
(blueprint: lem-pur-semilinear-tensor-presentation-transport)
-/

@[expose] public noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules.TensorPresentationTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Semilinear transport of the sheafified tensor, with its actual adjunct and scalars.

Source: integral-twist paragraph of sk-prop-sfb-cartesian-coefficients-twists.proof.md;
Stacks, Modules on Sites, Tags 03CY, 03D1--03D3, 03EK and 03EL.
(blueprint: lem-pur-semilinear-tensor-presentation-transport)

Proof:
1. Use lem-weil-pbc-geometric-module-transport with identity structural map to construct
   the algebraic inverse image over F(DY), with its transported operations and actual
   underlying adjunction. The normalized tensor comparison of
   lem-weil-pbc-algebraic-inverse-image-tensor-comparison identifies the pure pairing
   as a morphism on the full product sheaf, using that product as the test sheaf.
2. Sectionwise, A tensor_D B acts on M tensor_D B by
   (x tensor v)(m tensor w) = xm tensor vw. Additivity and balancing follow from the
   tensor relations; associativity and the unit follow on pure tensors. Restrictions
   preserve the action. The module sheafification interface
   lem-pc-sites-module-sheafification-interface extends it uniquely to the sheafified
   tensor ring and module. The pushout presentation identifies that ring with R,
   producing hY and hX. It does not assert a sectionwise pushout.
3. Semilinearity of s over a restricts to d-semilinearity by da_comm, and b is
   d-semilinear by db_comm. The pairing s(u) tensor b(v) is balanced over F(DY).
   lem-pc-sites-sheaf-tensor-bilinear-universal gives its map U. The pairing using
   s inverse and b inverse is its inverse, by the same universal property.
   Compose U with the normalized inverse-image tensor comparison to obtain r.
4. Unit naturality of the actual adjunction identifies the adjunct of r on the pure
   pairing with V of the target pairing applied to the actual adjuncts of s and b.
   The inverse product comparison for V is exactly the one in HasAdjunctFormula.
5. Two additive maps with that adjunct formula agree on every presheaf pure tensor,
   then on finite sums, and hence on the abelian sheafification. Injectivity of the
   adjunction hom equivalence proves uniqueness among all additive isomorphisms.
6. Applying F to the four-variable action formula and using the normalized pairing
   comparison shows that its inverse intertwines the tensor-ring actions. Identify
   maps after sheafification by the factorization clause of
   lem-pc-sites-module-sheafification-interface, not by assuming global pure generation.
7. The map U is semilinear for a tensor b by its pure-input formula; extend that
   equality through module sheafification by the same factorization clause. The
   compatibility with both presentation inclusions, iA_comm and iB_comm, is the
   stated c F(beta) equation and gives c-semilinearity of r on all local sections.
8. Sheafify 1 tensor q to obtain the additive coefficient maps jY and jX, with the
   displayed pure formulas. Naturality of the inverse-image tensor comparison and
   b' F(qY) = qX b identify the two composites on pure pairs. Their tensor universal
   property and sheafification give the naturality equation. The i-compatibility
   equations identify their scalar structures. No points or freeness are used.
-/
theorem exists_unique_semilinear_tensor_transport
    {C E : Type u} [Category.{u} C] [Category.{u} E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology E}
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    [PreservesFiniteLimits F]
    {DY AY : Sheaf J CommRingCat.{u}} {DX AX : Sheaf K CommRingCat.{u}}
    {daY : DY ⟶ AY} {daX : DX ⟶ AX}
    (Y : Presentation daY) (X : Presentation daX) (t : Transport F Y X)
    (MY : SheafOfModules.{u} (RingedTensor.ringSheaf AY))
    (MX : SheafOfModules.{u} (RingedTensor.ringSheaf AX))
    (s : F.obj (abSets (moduleAb MY)) ≅ abSets (moduleAb MX))
    (hs : IsAdditiveTransport F (moduleAb MY) (moduleAb MX) s)
    (hsa : IsSemilinearTransport F AY AX (moduleAb MY) (moduleAb MX)
      (fun U ↦ inferInstanceAs (SMul (AY.obj.obj U) (MY.val.obj U)))
      (fun U ↦ inferInstanceAs (SMul (AX.obj.obj U) (MX.val.obj U))) t.a s) :
    ∃ (hY : ∀ U : Cᵒᵖ, Module (Y.R.obj.obj U) ((tensorModule Y MY).val.obj U))
      (hX : ∀ U : Eᵒᵖ, Module (X.R.obj.obj U) ((tensorModule X MX).val.obj U)),
      IsTensorAction Y MY hY ∧ IsTensorAction X MX hX ∧
      ∃ r : F.obj (abSets (moduleAb (tensorModule Y MY))) ≅
          abSets (moduleAb (tensorModule X MX)),
        IsAdditiveTransport F (moduleAb (tensorModule Y MY))
          (moduleAb (tensorModule X MX)) r ∧
        HasAdjunctFormula F V adj Y X MY MX s t.b r ∧
        (∀ r₀ : F.obj (abSets (moduleAb (tensorModule Y MY))) ≅
            abSets (moduleAb (tensorModule X MX)),
          IsAdditiveTransport F (moduleAb (tensorModule Y MY))
            (moduleAb (tensorModule X MX)) r₀ →
          HasAdjunctFormula F V adj Y X MY MX s t.b r₀ → r₀ = r) ∧
        IsSemilinearTransport F Y.R X.R (moduleAb (tensorModule Y MY))
          (moduleAb (tensorModule X MX)) (fun U ↦ (hY U).toSMul)
          (fun U ↦ (hX U).toSMul) t.c r ∧
        ∀ (Y' : Presentation daY) (X' : Presentation daX) (t' : Transport F Y' X')
          (qY : CoefficientChange Y Y') (qX : CoefficientChange X X'),
          t'.d = t.d → t'.a = t.a →
          F.map ((sheafCompose J (CategoryTheory.forget CommRingCat)).map qY.q) ≫
            t'.b.hom = t.b.hom ≫
              (sheafCompose K (CategoryTheory.forget CommRingCat)).map qX.q →
          F.map ((sheafCompose J (CategoryTheory.forget CommRingCat)).map qY.i) ≫
            t'.c.hom = t.c.hom ≫
              (sheafCompose K (CategoryTheory.forget CommRingCat)).map qX.i →
          ∃ (jY : moduleAb (tensorModule Y MY) ⟶ moduleAb (tensorModule Y' MY))
            (jX : moduleAb (tensorModule X MX) ⟶ moduleAb (tensorModule X' MX)),
            IsTensorMap qY MY jY ∧ IsTensorMap qX MX jX ∧
            ∀ r' : F.obj (abSets (moduleAb (tensorModule Y' MY))) ≅
                abSets (moduleAb (tensorModule X' MX)),
              IsAdditiveTransport F (moduleAb (tensorModule Y' MY))
                (moduleAb (tensorModule X' MX)) r' →
              HasAdjunctFormula F V adj Y' X' MY MX s t'.b r' →
              F.map ((sheafCompose J (CategoryTheory.forget AddCommGrpCat)).map jY) ≫
                r'.hom = r.hom ≫
                  (sheafCompose K (CategoryTheory.forget AddCommGrpCat)).map jX := by
  sorry

end SheafOfModules.TensorPresentationTransport
