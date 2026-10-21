/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.RingedModelRestriction
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomTensorTotal
import Sheaf.Algebra.Homology.KFlatRHomCurrying
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Paper.RingedModelCurrying
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Restriction preserves evaluation-normalized currying

Source: Stacks Project, Tags 08JB, 0A90 and 0A96.
(blueprint: lem-weil-pbc-ringed-model-currying-coherence).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.LocalizationRHom

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- Successive restriction preserves the fixed evaluation-normalized currying map.
This statement supplies no currying isomorphism, coefficient comparison, or tensor
comparison: those maps have already been constructed. It concerns arbitrary K-flat
sheaf coefficients and locally K-flat complexes, without a localization hypothesis.

Source: Stacks 08JB, 0A90 and 0A96
(blueprint: lem-weil-pbc-ringed-model-currying-coherence).
Proof:
1. Choose functorial K-injective representatives. Restriction to a slice and further
slice restriction preserve K-injectives, since they have exact additive left adjoints.
Restriction is exact, so the restricted resolutions represent the restricted targets.
2. In degree n identify restricted Hom complexes by their product projections. At
W over V, the further localized category is C/W in both presentations. Restrict each
local linear map along that identification. This gives natural invertible chain maps:
restriction preserves the products and the differential d_I phi - (-1)^n phi d_P.
3. Descend these normalized chain comparisons through the derived localization in
both variables. Their equality on every further slice implies the displayed
successive-restriction equation. The exact-functor comparison used here is precisely
localizationRestrictionCompIso, whose underlying module comparison is the identity.
4. For S and P as in the statement, Hom(P|U,I|U) is K-injective because P|U is K-flat.
The construction of modelCurryIso therefore computes currying by the chain map which
sends a local section phi and a pure tensor s tensor p to phi(s)(p). Repeat on V.
5. Restriction of that evaluation is evaluation of the restricted section. The
coefficient isomorphism xi acts on s and its inverse acts contravariantly in Hom.
The natural tensor comparison is constructed by restricting the presheaf tensor and
then sheafifying; hence the coefficientComplexIso transport sends precisely the same
pure tensors to the same sections. Equality on pure tensors before sheafification,
then the coproduct and product universal properties, gives the chain square.
6. Apply Q to that square. The representative comparisons in KFlatRHom.curryIso
and the exact-restriction factorization in modelCurryIso are natural, so their
comparison maps cancel on the two routes. This gives the displayed derived equation.
The same argument for any derived target morphism follows from localization, with
no boundedness hypothesis on that target. Zero sheaves, zero rings, the empty site,
and zero complexes use the identical maps and universal properties. -/
theorem modelCurrying_restriction (R : Sheaf J CommRingCat.{u}) :
    ∃ (e : ∀ U : C,
      localizationRHom R ⋙ localizationDerivedRestriction R U ≅
        ((localizationDerivedRestriction R U).op.prod
          (localizationDerivedRestriction R U)) ⋙ localizationRHom (R.over U))
      (s : ∀ (U V : C) (a : V ⟶ U),
        localizationRHom (R.over U) ⋙ localizationDerivedOverMap R a ≅
          ((localizationDerivedOverMap R a).op.prod (localizationDerivedOverMap R a)) ⋙
            localizationRHom (R.over V)),
      (∀ (U V : C) (a : V ⟶ U) (L M : localizationDerived R),
        (localizationDerivedOverMap R a).map ((e U).hom.app (op L, M)) ≫
          (s U V a).hom.app
            (op ((localizationDerivedRestriction R U).obj L),
              (localizationDerivedRestriction R U).obj M) ≫
          (localizationRHom (R.over V)).map
            (X := (op ((localizationDerivedOverMap R a).obj
              ((localizationDerivedRestriction R U).obj L)),
              (localizationDerivedOverMap R a).obj
                ((localizationDerivedRestriction R U).obj M)))
            (Y := (op ((localizationDerivedRestriction R V).obj L),
              (localizationDerivedRestriction R V).obj M))
            (((localizationRestrictionCompIso R a).inv.app L).op,
              (localizationRestrictionCompIso R a).hom.app M) =
        (localizationRestrictionCompIso R a).hom.app
          ((localizationRHom R).obj (op L, M)) ≫ (e V).hom.app (op L, M)) ∧
      ∀ (U V : C) (a : V ⟶ U)
        (S : localizationModules (R.over U)) (T : localizationModules (R.over V))
        (ξ : (moduleOverMap R a).obj S ≅ T)
        (hS : KFlatRHom.flat (R.over U)
          ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj S))
        (hT : KFlatRHom.flat (R.over V)
          ((HomologicalComplex.single (localizationModules (R.over V)) (.up ℤ) 0).obj T))
        (P : CochainComplex (localizationModules R) ℤ)
        (hPU : KFlatRHom.flat (R.over U) ((localizationComplexRestriction R U).obj P))
        (hPV : KFlatRHom.flat (R.over V) ((localizationComplexRestriction R V).obj P))
        (N : localizationDerived R),
          (localizationDerivedOverMap R a).map ((modelCurryIso R U S hS P hPU N).hom) ≫
            (s U V a).hom.app
              (op ((localizationQ (R.over U)).obj ((coefficientComplex R U S).obj P)),
                (localizationDerivedRestriction R U).obj N) ≫
            (localizationRHom (R.over V)).map
              (X := (op ((localizationDerivedOverMap R a).obj
                ((localizationQ (R.over U)).obj ((coefficientComplex R U S).obj P))),
                (localizationDerivedOverMap R a).obj
                  ((localizationDerivedRestriction R U).obj N)))
              (Y := (op ((localizationQ (R.over V)).obj
                ((coefficientComplex R V T).obj P)),
                (localizationDerivedRestriction R V).obj N))
              (((coefficientDerivedComplexIso R a S T ξ).inv.app P).op,
                (localizationRestrictionCompIso R a).hom.app N) =
          (s U V a).hom.app
            (op (derivedCoefficient R U S),
              (localizationRHom (R.over U)).obj
                (op ((localizationDerivedRestriction R U).obj ((localizationQ R).obj P)),
                  (localizationDerivedRestriction R U).obj N)) ≫
            (localizationRHom (R.over V)).map
              (X := (op ((localizationDerivedOverMap R a).obj
                (derivedCoefficient R U S)),
                (localizationDerivedOverMap R a).obj ((localizationRHom (R.over U)).obj
                  (op ((localizationDerivedRestriction R U).obj ((localizationQ R).obj P)),
                    (localizationDerivedRestriction R U).obj N))))
              (Y := (op (derivedCoefficient R V T),
                (localizationRHom (R.over V)).obj
                  (op ((localizationDerivedRestriction R V).obj ((localizationQ R).obj P)),
                    (localizationDerivedRestriction R V).obj N)))
              ((derivedCoefficientIso R a S T ξ).inv.op,
                (s U V a).hom.app
                  (op ((localizationDerivedRestriction R U).obj ((localizationQ R).obj P)),
                    (localizationDerivedRestriction R U).obj N) ≫
                (localizationRHom (R.over V)).map
                  (X := (op ((localizationDerivedOverMap R a).obj
                    ((localizationDerivedRestriction R U).obj ((localizationQ R).obj P))),
                    (localizationDerivedOverMap R a).obj
                      ((localizationDerivedRestriction R U).obj N)))
                  (Y := (op ((localizationDerivedRestriction R V).obj ((localizationQ R).obj P)),
                    (localizationDerivedRestriction R V).obj N))
                  (((localizationRestrictionCompIso R a).inv.app ((localizationQ R).obj P)).op,
                    (localizationRestrictionCompIso R a).hom.app N)) ≫
            (modelCurryIso R V T hT P hPV N).hom := by
  sorry

end CategoryTheory.LocalizationRHom
