/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenInterchangeReductionData

/-! Constructor case for structural word substitution.
Source: current blueprint fix-prop-coherence, structural substitution step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u s i
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.OpenInterchangeReduction

/-- The structuralReductionPushComposition component of structural word substitution.
The substitution argument reconstructs child systems, applies the bounded square to
a short skeleton, and pastes naturality; this statement isolates one constructor.
(blueprint: lem-sf-structural-reduction-word-substitution-PushComposition)
-/
theorem structuralReductionPushComposition
    {D : FiniteFieldDatum.{u}} (coeff : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic coeff.l) E]
    [FiniteDimensional (Padic coeff.l) E]
    (o : GeneratorReduction.Operations coeff.l E)
    (_hShort : ∀ {S : Type s} (W : S → Scheme.{u})
      (_hW : GeneratorReduction.FiniteTypeFamily W D.k)
      {I : Type i} (location : I → S)
      {a : S} {B C : GeneratorReduction.Word W location a}
      (g : GeneratorReduction.GeneratorKind W location B C),
      Structural g → B.length ≤ 3 → C.length ≤ 3 →
      ∀ (K : ∀ k : I, DerivedCategory (scalarReductionSource coeff.l E (W (location k))))
        (lo hi torLo torHi : ℤ),
        (∀ k : I, GeneratorReduction.Admissible coeff.l E
          (IntegralSystemRealization.calculus coeff.l E (W (location k))) (K k)
          lo hi torLo torHi) →
        GeneratorReduction.Word.admissible coeff.l E W location o K lo hi torLo torHi B →
        GeneratorReduction.Word.admissible coeff.l E W location o K lo hi torLo torHi C →
        GeneratorReduction.Assertion coeff.l E W location o K g)
    {S : Type s} (W : S → Scheme.{u})
    (_hW : GeneratorReduction.FiniteTypeFamily W D.k)
    {I : Type i} (location : I → S)
    {{a b c : S}}
    (f : W a ⟶ W b) (g : W b ⟶ W c)
    (hsf : IsSeparated f) (htf : LocallyOfFiniteType f) (hqf : QuasiCompact f)
    (hpf : IsProper f) (hsg : IsSeparated g) (htg : LocallyOfFiniteType g)
    (hqg : QuasiCompact g) (hpg : IsProper g)
    (hs : IsSeparated (f ≫ g)) (ht : LocallyOfFiniteType (f ≫ g))
    (hq : QuasiCompact (f ≫ g)) (hp : IsProper (f ≫ g))
    {{B : GeneratorReduction.Word W location a}}
    (K : ∀ k : I, DerivedCategory (scalarReductionSource coeff.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (_hAdm : ∀ k : I, GeneratorReduction.Admissible coeff.l E
      (IntegralSystemRealization.calculus coeff.l E (W (location k))) (K k)
      lo hi torLo torHi)
    (hB : GeneratorReduction.Word.admissible coeff.l E W location o K lo hi torLo torHi
      (GeneratorReduction.Word.push g hsg htg hqg hpg
        (GeneratorReduction.Word.push f hsf htf hqf hpf B)))
    (hC : GeneratorReduction.Word.admissible coeff.l E W location o K lo hi torLo torHi
      (GeneratorReduction.Word.push (f ≫ g) hs ht hq hp B)) :
    GeneratorReduction.Assertion coeff.l E W location o K
    (GeneratorReduction.GeneratorKind.pushComposition f g hsf htf hqf hpf hsg htg hqg hpg
      hs ht hq hp B) := by
  sorry

end WeilConjectures.OpenInterchangeReduction
