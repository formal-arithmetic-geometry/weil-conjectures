/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars

/-!
# Linear descent across localization of an algebra sheaf

Source: Stacks Project, sites-modules.tex, Tag 0EMD (lemma-simple-invert-module),
applied to the underlying module of an algebra and restriction of scalars.
(blueprint: lem-sfb-localization-linear-descent)
-/

@[expose] public section

set_option autoImplicit false

universe uC vC w

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory.Mod

/-- In a localization square of commutative algebra sheaves, the localized algebra,
viewed as a module over the localized base, represents extension of linear maps.
There is no finiteness, basis, injectivity or torsion-freeness assumption.

Source: Stacks Project, sites-modules.tex, Tag 0EMD (lemma-simple-invert-module),
with the localization model of Tag 0EMC (lemma-simple-invert).
(blueprint: lem-sfb-localization-linear-descent)

Proof:
1. Pass to a small equivalent site in the coefficient universe, transporting the
sheaf tensor and internal rings and modules along the induced monoidal equivalence.
Reconstruct section rings and sectionwise modules using the monoidal sheafification
adjunction. A global section gives compatible sections of all
section rings. Invertibility of its multiplication map is equivalent to existence
of a compatible multiplicative inverse: apply the inverse map to the ring unit.
2. Identify both given ring localizations with sheafifications of sectionwise
localizations using Tag 0EMC and uniqueness of its universal maps. Their square
identifies the two images of t. The restriction of any A-module N is therefore an
R-module on which t acts invertibly.
3. Given the R-linear map f:T→N, extend on fractions by
u/φ(t)^n ↦ jR(t)^(-n) f(u). If two fractions agree, a further power of φ(t)
kills their cross-multiplied difference. R-linearity and invertibility on N
make their two proposed images equal. This also proves addition compatibility;
no cancellation in R or T is used. Uniqueness on u/1 makes the maps natural
under restriction, so the sheafification adjunction gives a unique map B→N.
4. This map is A-linear. Locally any scalar of A has the form r/t^m. On local
fractions the desired identity is
jR(t)^(-n-m) f(φ(r)u) = jR(r) jR(t)^(-n-m) f(u).
This follows from R-linearity; separatedness gives the equality on all sections.
The localization and sheafification uniqueness clauses prove uniqueness among
A-linear maps. The same formulas apply to t=0 and to zero modules.
-/
theorem sheaf_localization_linearDescent
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    letI : MonoidalCategory (Sheaf J Ab.{w}) :=
      (sfbSheafTensorStructure (A := Ab.{w}) J).monoidal
    letI : BraidedCategory (Sheaf J Ab.{w}) :=
      (sfbSheafTensorStructure (A := Ab.{w}) J).symmetric.toBraidedCategory
    ∀ (R T A B : Sheaf J Ab.{w})
      [MonObj R] [MonObj T] [MonObj A] [MonObj B]
      [IsCommMonObj R] [IsCommMonObj T] [IsCommMonObj A] [IsCommMonObj B]
      (φ : Mon.mk R ⟶ Mon.mk T) (t : 𝟙_ (Sheaf J Ab.{w}) ⟶ R)
      (jR : Mon.mk R ⟶ Mon.mk A) (jT : Mon.mk T ⟶ Mon.mk B)
      (ψ : Mon.mk A ⟶ Mon.mk B),
      jR ≫ ψ = φ ≫ jT →
      IsIso ((λ_ A).inv ≫ (t ≫ jR.hom) ▷ A ≫ μ[A]) →
      (∀ (D : Sheaf J Ab.{w}) [MonObj D] [IsCommMonObj D]
        (f : Mon.mk R ⟶ Mon.mk D),
        IsIso ((λ_ D).inv ≫ (t ≫ f.hom) ▷ D ≫ μ[D]) →
        ∃! g : Mon.mk A ⟶ Mon.mk D, jR ≫ g = f) →
      IsIso ((λ_ B).inv ≫ (t ≫ φ.hom ≫ jT.hom) ▷ B ≫ μ[B]) →
      (∀ (D : Sheaf J Ab.{w}) [MonObj D] [IsCommMonObj D]
        (f : Mon.mk T ⟶ Mon.mk D),
        IsIso ((λ_ D).inv ≫ (t ≫ φ.hom ≫ f.hom) ▷ D ≫ μ[D]) →
        ∃! g : Mon.mk B ⟶ Mon.mk D, jT ≫ g = f) →
      ∀ (N : Mod (Sheaf J Ab.{w}) A)
        (f : (comap φ.hom).obj (regular T) ⟶ (comap jR.hom).obj N),
        ∃! g : (comap ψ.hom).obj (regular B) ⟶ N,
          jT.hom ≫ g.hom = f.hom := by
  sorry

end CategoryTheory.Mod
