/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.Algebra.Homology.LocalizedTensorComparisonProperty
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.RingTheory.Flat.Basic

/-! # The coefficient comparison on K-flat complexes

Source: Stacks Project, Tags 06Y6, 0BYJ, and 0DJ7.
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat
variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- The localized coefficient comparison is natural on K-flat complexes.

Source: Stacks Project, Tag 06Y6 (derived change of rings), Tag 0BYJ
(associativity), and perfect.tex, equation-bc before Tag 0DJ7.

Proof: tensor the input with Q, restrict to R, apply the universal left derived
extension to B, and take degree-i cohomology. Multiplication by A commutes with
these functorial maps and with multiplication by B; the R-actions agree.
The tensor-action construction, applied objectwise and transported along
these functorial maps, supplies an E=A-tensor-R-B-linear source functor.
Extend that functor from E to C. A quasi-isomorphism of inputs stays a
quasi-isomorphism after tensor with the K-flat Q, restriction to R is exact, and
the derived extension and cohomology send it to an isomorphism. Extension to C
preserves this isomorphism, so the source functor inverts these morphisms.
Compose the universal derived counit with the ordinary coefficient natural
map into restriction of C-extension. Take homology and its exact restriction
identification. Naturality at A-multiplication makes the components E-linear.
Transpose through E-to-C extension and restriction, and compose with tensor
rebracketing and identity tensor t. Each of these maps is natural on chain maps.
Its square follows from naturality of the tensorator and whisker exchange.
For each canonical universal model m, uniqueness of its derived counit supplies
the cohomology isomorphism with the source functor. The scalar-action equations
make it E-linear, and extending it to C gives e. The ordinaryIso and
ordinaryToLocalized equations agree on generators; comparison_eq and
localized_eq then identify e followed by the natural comparison with the
stated component. This only constructs the natural transformation on K-flat
complexes: target inversion and descent to D(A) are separate steps. No
invertibility of the comparison or K-flatness of N is used. Zero complexes,
zero rings, and unbounded complexes are covered by the same tensor sums.
(blueprint: lem-pc-kflat-localized-tensor-comparison-natural). -/
theorem exists_kFlatLocalizedTensorComparison_natural
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    (i : ℤ) :
    let m := fun U : CochainComplex.KFlat (ModuleCat.{u} A) ↦
      baseDerivedTensorCohomologyModel R A B (U.obj ⊗ Q) C
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let T := CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ F ⋙ tensorRight N ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) i
    ∃ (S : CochainComplex.KFlat (ModuleCat.{u} A) ⥤ ModuleCat.{u} C)
      (η : S ⟶ T),
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).WKFlat.IsInvertedBy S ∧
      ∀ U : CochainComplex.KFlat (ModuleCat.{u} A),
        ∃ e : (extendScalars (algebraMap (A ⊗[R] B) C)).obj ((m U).cohomology i) ≅
          S.obj U,
          e.hom ≫ η.app U = (m U).localizedComparison i ≫
            HomologicalComplex.homologyMap
              ((Functor.Monoidal.μIso F U.obj Q).inv ≫ (F.obj U.obj ◁ t)) i := by sorry

end ModuleCat
