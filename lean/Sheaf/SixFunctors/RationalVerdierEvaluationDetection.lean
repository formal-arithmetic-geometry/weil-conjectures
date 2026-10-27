/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.SixFunctors.RationalVerdierModels

/-! # Nondegeneracy of normalized rational evaluation

Source: blueprint thm-coef-rational-verdier, evaluation and transposition.
(blueprint: lem-coef-rational-verdier-evaluation-detection). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (w : IntegralFiniteExtension.DualizingDatum l X D hl E)

/-- The normalized rational evaluation detects maps into its dual object.
Source: blueprint thm-coef-rational-verdier, paragraph 1, evaluation and transposition;
Stacks 08J9. (blueprint: lem-coef-rational-verdier-evaluation-detection).

Proof: identify the rational dual with the localized restricted integral internal Hom
using A.objects. For fixed integral K and V, the ordinary tensor-Hom adjunction gives
an O_E-linear bijection from Hom(V,RHom(K,omega)) to Hom(K tensor V,omega). Its inverse
is composition of the ordinary tensor arrow with the ordinary counit; linearity follows
from the normalized internal Hom and the adjunction identities. Conjugate the target
by the invertible completion comparison on (K,V). Naturality of completion identifies
the resulting map with completed tensor followed by integral evaluation. Tensor this
linear equivalence with the localized coefficient ring. The rational tensor's bilinear
pure-tensor equation, the pure-tensor composition equation, and A.evaluation_integral
identify its action on every pure tensor with rational tensor followed by evaluation.
Both maps are additive, so the identity extends to arbitrary localized morphisms.
This base-changed linear equivalence is injective, giving f=g. Every raw rational K,V
has its stored integral object as representative, so the argument covers every input;
zero objects and the empty scheme cause no exception. -/
theorem rational_evaluation_detect (A : Datum D l hl X E w)
    (K V : sfRationalConstructibleCategory l E X)
    (f g : V ⟶ A.dual.obj (op K))
    (h : (tensor D l hl X E).map (Prod.mkHom (𝟙 K) f) ≫ A.evaluation K =
      (tensor D l hl X E).map (Prod.mkHom (𝟙 K) g) ≫ A.evaluation K) : f = g := by sorry

end WeilConjectures.RationalVerdier
