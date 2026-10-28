/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.Paper.IntegralHomReductionModels
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # Transport of normalized integral Hom counits

Source: Stacks Project, sites-cohomology.tex, Lemma 08J9.
(blueprint: lem-sf-integral-hom-evaluation-transport).

The supplied normalized tensor presentation is compared with a native closed
structure.  The comparison is the part requiring the representative calculation;
the naturality theorem itself is then a formal consequence.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralHom

noncomputable def swapTensor {D : Type*} [Category D] (T : D × D ⥤ D) :
    D × D ⥤ D := Functor.uncurry.obj (Functor.flip (Functor.curry.obj T))

noncomputable def transportedCounit (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R)
    (S : CoefficientClosedStructure (hom.{u, u} X R))
    (e : a.tensor ≅ swapTensor S.tensor) (K W : Derived.{u, u} X R) :
    ((Functor.curry.obj (hom.{u, u} X R)).obj (op K) ⋙
      (Functor.curry.obj a.tensor).obj K).obj W ⟶ W := by
  with_unfolding_all
    exact e.hom.app (K, (hom.{u, u} X R).obj (op K, W)) ≫
      (S.adjunction K).counit.app W

/-- The supplied counits are the transport of a closed native counit.

Source: Stacks Project, sites-cohomology.tex, Lemma 08J9, K-flat comparison and
Hom-complex evaluation.  Proof: compare the supplied representative with the
native K-flat tensor comparison by full faithfulness of the product localization.
Use the opposite tensor order for the supplied presentation.  On K-flat source
and K-injective target, the two counits have the same signed pure-tensor formula
by `TensorPresentation.evaluation`; K-flat and K-injective resolutions extend the
equality to all derived objects.  The construction is independent of choices and
applies to unbounded complexes.
(blueprint: lem-sf-integral-hom-evaluation-transport). -/
theorem tensorPresentation_counit_transport (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R) :
    ∃ S : CoefficientClosedStructure (hom.{u, u} X R),
      ∃ e : a.tensor ≅ swapTensor S.tensor,
        ∀ (K W : Derived.{u, u} X R),
          transportedCounit X R a S e K W = (a.adjunction K).counit.app W := by
  sorry

/-- The transported native counits are natural in the first tensor variable.

Source: Stacks Project, sites-cohomology.tex, Lemma 08J9.  Proof: expand
`transportedCounit`; naturality of `e` changes the supplied tensor map into the
swapped native tensor map, and `CoefficientClosedStructure.evaluation_naturality`
then gives the equality.  This is a purely formal categorical calculation.
(blueprint: lem-sf-integral-hom-evaluation-transport-naturality). -/
theorem transportedCounit_naturality (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R)
    (S : CoefficientClosedStructure (hom.{u, u} X R))
    (e : a.tensor ≅ swapTensor S.tensor)
    (K K' W : Derived.{u, u} X R) (f : K' ⟶ K) :
    a.tensor.map (Prod.mkHom (𝟙 K')
      ((hom.{u, u} X R).map (Prod.mkHom f.op (𝟙 W)))) ≫
        transportedCounit X R a S e K' W =
      a.tensor.map (Prod.mkHom f (𝟙 _)) ≫
        transportedCounit X R a S e K W := by
  with_unfolding_all
    simp only [transportedCounit]
    erw [e.hom.naturality_assoc, e.hom.naturality_assoc]
    congr 1
    simpa [swapTensor, CoefficientClosedStructure.tensor] using
      S.evaluation_naturality K K' W f

end WeilConjectures.IntegralHom
