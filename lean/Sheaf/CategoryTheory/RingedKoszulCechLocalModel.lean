/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem

/-! # A local normalized Cech--Koszul model

Source: Stacks Project, Tags 0A0A, 0941 and 099B. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

/-- A single ringed site has a unit-normalized strict-limit model. Only the local
comparison and the separating property of its unit are asserted here; no slice
comparisons or coherence are included.
Source: Stacks Project, Cohomology on Sites, Tags 0A0A and 0941; algebraization.tex,
Tag 099B, uniqueness in the derived-completion reflection property.
(blueprint: lem-weil-pbc-ringed-koszul-cech-local-model).

Proof: replace N functorially by a K-injective I. The augmented telescope of positive
Koszul complexes is quasi-isomorphic to Cech. Hom from that telescope into I is the
fibre of 1-shift on the product of Hom(P_m,I). Finite free evaluation identifies these
with I tensor Q_m, including the total-tensor signs and inverse transitions.
The finite split-perfect tensor theorem makes each term K-injective, so termwise
products compute derived products. Resolve the strict tower by a degreewise-injective
K-injective tower. Its evaluations are K-injective; comparison maps between them and
the preceding terms are homotopy equivalences, as are their products. Injectivity
splits each transition of the resolved tower. The recursion x_0=0 and
x_(m+1)=sigma_m(x_m-y_m) splits 1-shift; its kernel is the ordinary limit. The
kernel-to-fibre quasi-isomorphism identifies that limit with the Roos fibre.
K-flatness of Q_m permits replacing N by I before taking total derived inverse limit.
Descend these specified natural maps through localization to obtain D and theta.
The positive projections send x to (0,(x)_m) in the fibre, so theta preserves the
strict units. These units are natural. The Cech completion reflection property
(Tag 099B) makes precomposition injective into every completion object; transport
this property across theta. For the empty list the diagonal I is the kernel of
1-shift on the constant tower, and its map is the strict unit, hence an isomorphism. -/
theorem ringedKoszul_cech_local_model :
    ∃ (D : RingedKoszulLimitPresentation O r b)
      (theta : ringedCechCompletionFunctor O (ringedExtendedCech O r b).1 ≅ D.completion),
      (∀ E, ringedCechCompletionUnit O (ringedExtendedCech O r b).1
        (ringedExtendedCech O r b).2 E ≫ theta.hom.app E = D.unit E) ∧
      (∀ E X, Function.Injective
        (fun f : D.completion.obj E ⟶ D.completion.obj X ↦ D.unit E ≫ f)) ∧
      (∀ E E' (f : E ⟶ E'), D.unit E ≫ D.completion.map f = f ≫ D.unit E') ∧
      (r = 0 → ∀ E, IsIso (D.unit E)) := by sorry

end CategoryTheory
