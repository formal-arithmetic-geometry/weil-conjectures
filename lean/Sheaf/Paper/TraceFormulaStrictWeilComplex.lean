/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.SchemeFrobenius
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Strict Weil complexes at finite coefficients

Source: Weil conjectures blueprint, main-20261015,
sec-smooth-purity/sk-def-sf-weil-complexes/def-trf-strict-weil-complex.md, order 2509
(blueprint: def-trf-strict-weil-complex).

The fixed pairs are formed in the recorded ambient derived category of modules over
the constant coefficient ring sheaf on the small pro-etale site. Their carriers satisfy
the recorded bounded constructible finite-Tor predicate. Thus the structure isomorphism
is ambient, and the definition needs no theorem restricting pullback to that subcategory.
Morphisms and composition are those of the existing fixed-pair category `IsoAlgebra`.
No triangulated structure or derived category of Weil sheaves is asserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry.Scheme

namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- The derived pullback `Lg_γ^*` along the recorded geometric Galois Frobenius,
at exactly the coefficient ring and positive level fixed by `T`.
Source: main-20261015 blueprint, order 2509
(blueprint: def-trf-strict-weil-complex). -/
def strictWeilFrobeniusPullback (T : TraceFormulaCoefficientConventions.{u}) :
    proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing ⥤
      proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing :=
  T.derivedPullback (T.datum.geometricGaloisFrobenius T.X₀)

/-- The underlying complex of a Frobenius-fixed pair lies in `Dᵇ_ctf(X,A)`.
This uses the coefficient conventions' predicate without defining constructibility
or Tor amplitude again. Source: main-20261015 blueprint, order 2509
(blueprint: def-trf-strict-weil-complex). -/
def strictWeilCarrierProperty (T : TraceFormulaCoefficientConventions.{u}) :
    ObjectProperty (IsoAlgebra T.strictWeilFrobeniusPullback) :=
  T.boundedConstructibleFiniteTor.inverseImage (IsoAlgebra.forget _)

/-- The category `Dᵇ_ctf,W(X,A)` of strict Weil pairs `(K,φ : Lg_γ^* K ≅ K)`.
The full subcategory condition is imposed only on `K`; the isomorphism is in the
ambient derived category. A morphism is an underlying arrow `u` with
`φ.hom ≫ u = (Lg_γ^*).map u ≫ φ'.hom`, with inherited identities and composition.
These are pairs over `Dᵇ_ctf`, as in the rational fixed-pair convention, and their
Hom sets are not defined by taking Ext groups of Weil sheaves.
Source: main-20261015 blueprint, order 2509
(blueprint: def-trf-strict-weil-complex). -/
abbrev strictWeilComplex (T : TraceFormulaCoefficientConventions.{u}) : Type _ :=
  T.strictWeilCarrierProperty.FullSubcategory

/-- The forgetful functor `For`, retaining the underlying bounded constructible
finite-Tor complex and its underlying arrows. It is the lift of the existing
fixed-pair forgetful functor to the recorded full subcategory `Dᵇ_ctf(X,A)`.
Source: main-20261015 blueprint, order 2509
(blueprint: def-trf-strict-weil-complex). -/
def strictWeilForget (T : TraceFormulaCoefficientConventions.{u}) :
    T.strictWeilComplex ⥤ T.boundedConstructibleFiniteTor.FullSubcategory :=
  T.boundedConstructibleFiniteTor.lift
    (T.strictWeilCarrierProperty.ι ⋙ IsoAlgebra.forget _) (fun K ↦ K.property)

/-- The structure isomorphism of a strict Weil complex, with underlying object
given by `For`. Source: main-20261015 blueprint, order 2509
(blueprint: def-trf-strict-weil-complex). -/
def strictWeilFrobenius (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) :
    T.strictWeilFrobeniusPullback.obj ((T.strictWeilForget.obj K).obj) ≅
      (T.strictWeilForget.obj K).obj :=
  K.obj.str

end WeilConjectures.TraceFormulaCoefficientConventions
