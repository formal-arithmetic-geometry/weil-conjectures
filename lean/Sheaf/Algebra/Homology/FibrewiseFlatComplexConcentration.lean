/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.FlatModInjective
import Mathlib.RingTheory.Flat.Equalizer
import Sheaf.RingTheory.UniversalInjectiveCheckStalks
import Sheaf.TraceFormula.UniversallyExactFlatSubmodule
import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer

/-! # Universal concentration of a finite flat complex from its fibres

Source: Stacks Project, dualizing.tex, Tag 0E2F, final two paragraphs, using algebra.tex,
Tag 00ME (blueprint: lem-sfb-fibrewise-flat-complex-concentration).

The truncation is Mathlib's good truncation. The natural transformation `b` is fixed by
its degree-zero component, the quotient from cycles to cohomology. The isomorphism in
the derived category is normalized by the two actual scalar-extended zigzag arrows.
Extension of scalars along S → S tensor_R R' is the canonical presentation of termwise
R-extension, with its full S tensor_R R' action. No property of R' is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w x z

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ModuleCat

/-- Canonical associativity of scalar extension at independent ring universes.
This is the adjoint mate of the identity-on-elements comparison for restriction;
it is the same construction as Mathlib's `extendScalarsComp`, whose ring universes
are specialized to be equal. It sends t tensor m to t tensor (1 tensor m).
Source: Stacks Project, Tag 0E2F, compatibility with successive scalar extension
(blueprint: lem-sfb-fibrewise-flat-complex-concentration). -/
def extendScalarsCompOfUniverses
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    extendScalars.{u, w, max u v w x} (g.comp f) ≅
      extendScalars.{u, v, max u v w x} f ⋙ extendScalars.{v, w, max u v w x} g :=
  (conjugateIsoEquiv
    ((extendRestrictScalarsAdj.{max u v w x, u, v} f).comp
      (extendRestrictScalarsAdj.{max u v w x, v, w} g))
    (extendRestrictScalarsAdj.{max u v w x, u, w} (g.comp f))).symm
      (restrictScalarsComp.{max u v w x} f g).symm

end ModuleCat

namespace CochainComplex

/-- Fibrewise concentration gives the specified universal truncation zigzag.
Source: Stacks Project, Tag 0E2F, final two paragraphs, and Tag 00ME
(blueprint: lem-sfb-fibrewise-flat-complex-concentration).

Proof:
1. Put Q^n = coker(d^{n-1}). These are finite S-modules. Right exactness of tensor
   identifies their tensor products with the corresponding cokernels. For n ≠ 0,
   fibrewise concentration says Q^n tensor κ(p) → E^{n+1} tensor κ(p) is injective.
2. Localize at q in Spec S and p = q ∩ R. Localization preserves exactness, finiteness,
   and R-flatness, and localization commutes with tensor over the base. The induced
   local ring map R_p → S_q and the residue-field tensor satisfy Tag 00ME's hypotheses.
3. Apply flat_mod_injective to obtain injectivity with flat cokernel. The flat-quotient
   tensor lemma and universally_injective_iff_localizedAtContractedPrime make each
   Q^n → E^{n+1}, n ≠ 0, universally injective over R.
4. Thus every nonzero-degree cohomology vanishes after tensor with any R-module.
   Universal exactness and flat_submodule_of_universally_exact make Q^1 flat. The
   flat-kernel lemma then makes B^1 = im(d^0) flat.
5. Tensor 0 → Z^0 → E^0 → B^1 → 0 and 0 → B^1 → E^1 → Q^1 → 0. Both stay exact;
   consequently Z^0 tensor L is precisely the kernel of d^0 tensor L.
6. Since H^0(E) is flat, tensoring 0 → B^0 → Z^0 → H^0(E) → 0 stays exact too.
   Right exactness preserves the surjection E^{-1} → B^0. Hence the inclusion and the
   quotient in the specified zigzag induce the same degree-zero cohomology isomorphism;
   negative cohomology agrees with that of E tensor L, and positive cohomology is zero.
   Taking L = R' proves both quasi-isomorphisms as S tensor_R R'-complexes.
7. Chain maps preserve cycles and boundaries, so the quotient maps form the natural
   transformation b, and inclusion is natural as well. Tensor associativity commutes
   with both arrows; its pure-tensor formula multiplies the scalar factors, so further
   extensions, including identity and triple extensions, agree. Localization inverts
   the left arrow a and right arrow b, giving Q(a)^{-1} ≫ Q(b). The displayed equation
   fixes exactly this isomorphism and the commuting zigzag squares imply its naturality.
   No flatness or Noetherianity of the extension ring is used. -/
theorem fibrewiseFlat_complex_concentration
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (E : CochainComplex (ModuleCat.{max u v w x} S) ℤ)
    (hbelow : ∃ N : ℤ, ∀ n : ℤ, n < N → IsZero (E.X n))
    (hfinite : ∀ n : ℤ, Module.Finite S (E.X n))
    (hflat : ∀ n : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R S)).obj (E.X n)))
    (hfibres : ∀ (p : PrimeSpectrum R) (i : ℤ), i ≠ 0 → IsZero
      ((((ModuleCat.extendScalars.{_, _, max u v w x}
        (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom)
          |>.mapHomologicalComplex (.up ℤ)).obj E).homology i))
    (hzero : Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R S)).obj (E.homology 0))) :
    ∃ b : (ComplexShape.embeddingUpIntLE 0).truncLEFunctor (ModuleCat.{max u v w x} S) ⟶
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v w x} S) (.up ℤ) 0 ⋙
          CochainComplex.singleFunctor (ModuleCat.{max u v w x} S) 0,
      (∀ K : CochainComplex (ModuleCat.{max u v w x} S) ℤ,
        (b.app K).f 0 = (K.truncLEXIsoCycles 0).hom ≫ K.homologyπ 0 ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (K.homology 0)).inv) ∧
      (∀ (R' : Type x) [CommRing R'] [Algebra R R']
          [HasDerivedCategory.{z} (ModuleCat.{max u v w x} (S ⊗[R] R'))],
        QuasiIso (((ModuleCat.extendScalars.{_, _, max u v w x} (algebraMap S (S ⊗[R] R')))
          |>.mapHomologicalComplex (.up ℤ)).map (E.ιTruncLE 0)) ∧
        QuasiIso (((ModuleCat.extendScalars.{_, _, max u v w x} (algebraMap S (S ⊗[R] R')))
          |>.mapHomologicalComplex (.up ℤ)).map (b.app E)) ∧
        ∃ e : DerivedCategory.Q.obj
            (((ModuleCat.extendScalars.{_, _, max u v w x} (algebraMap S (S ⊗[R] R')))
              |>.mapHomologicalComplex (.up ℤ)).obj E) ≅
            DerivedCategory.Q.obj
              (((ModuleCat.extendScalars.{_, _, max u v w x} (algebraMap S (S ⊗[R] R')))
                |>.mapHomologicalComplex (.up ℤ)).obj
                  ((CochainComplex.singleFunctor _ 0).obj (E.homology 0))),
          DerivedCategory.Q.map
              (((ModuleCat.extendScalars.{_, _, max u v w x} (algebraMap S (S ⊗[R] R')))
                |>.mapHomologicalComplex (.up ℤ)).map (E.ιTruncLE 0)) ≫ e.hom =
            DerivedCategory.Q.map
              (((ModuleCat.extendScalars.{_, _, max u v w x} (algebraMap S (S ⊗[R] R')))
                |>.mapHomologicalComplex (.up ℤ)).map (b.app E))) ∧
      (∀ (B C : Type (max v x)) [CommRing B] [CommRing C]
          (f : S →+* B) (g : B →+* C),
        ((ModuleCat.extendScalars.{_, _, max u v w x} (g.comp f)).mapHomologicalComplex (.up ℤ)).map
            (E.ιTruncLE 0) ≫
            (NatIso.mapHomologicalComplex
              (ModuleCat.extendScalarsCompOfUniverses.{v, max v x, max v x, max u v w x} f g)
              (.up ℤ)).hom.app E =
          (NatIso.mapHomologicalComplex
              (ModuleCat.extendScalarsCompOfUniverses.{v, max v x, max v x, max u v w x} f g)
              (.up ℤ)).hom.app (E.truncLE 0) ≫
            ((ModuleCat.extendScalars.{_, _, max u v w x} f ⋙
                ModuleCat.extendScalars.{_, _, max u v w x} g).mapHomologicalComplex (.up ℤ)).map
                (E.ιTruncLE 0) ∧
        ((ModuleCat.extendScalars.{_, _, max u v w x} (g.comp f)).mapHomologicalComplex (.up ℤ)).map
            (b.app E) ≫
            (NatIso.mapHomologicalComplex
              (ModuleCat.extendScalarsCompOfUniverses.{v, max v x, max v x, max u v w x} f g)
              (.up ℤ)).hom.app ((CochainComplex.singleFunctor _ 0).obj (E.homology 0)) =
          (NatIso.mapHomologicalComplex
              (ModuleCat.extendScalarsCompOfUniverses.{v, max v x, max v x, max u v w x} f g)
              (.up ℤ)).hom.app (E.truncLE 0) ≫
            ((ModuleCat.extendScalars.{_, _, max u v w x} f ⋙
                ModuleCat.extendScalars.{_, _, max u v w x} g).mapHomologicalComplex (.up ℤ)).map
                (b.app E)) := by
  sorry

end CochainComplex
