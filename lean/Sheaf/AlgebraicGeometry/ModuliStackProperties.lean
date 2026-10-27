/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Smoothness, finite type and separatedness for moduli stacks

Source: Stacks Project, stacks-morphisms.tex, Definitions `definition-separated`,
`definition-smooth`, and `definition-locally-finite-type` and Section `section-finite-type`
(blueprint: def-sfb-moduli-stack-properties).

For DM stacks, smoothness and finite type can be tested on a quasi-compact étale atlas.
A proper DM diagonal is quasi-finite and therefore finite, so its scheme base changes
are schemes. Both projections of each diagonal base change are retained below.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A smooth finite-type atlas for a DM stack over a field: an étale surjective scheme
atlas whose structure morphism is smooth and of finite type, including quasi-compactness.
Source: Stacks Project, stacks-morphisms.tex, Sections `section-smooth`,
`section-finite-type` (blueprint: def-sfb-moduli-stack-properties). -/
def HasSmoothFiniteTypeModuliAtlas {k : Type u} [Field k]
    (F : BasedCategory.{v, w} (Over (AlgebraicGeometry.Spec (.of k)))) : Prop :=
  ∃ (U : Over (AlgebraicGeometry.Spec (.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
    AlgebraicGeometry.Smooth U.hom ∧ AlgebraicGeometry.LocallyOfFiniteType U.hom ∧
    AlgebraicGeometry.QuasiCompact U.hom ∧
    ∀ (T : Over (AlgebraicGeometry.Spec (.of k)))
        (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
      ∃ (Z : AlgebraicGeometry.AlgebraicSpace (AlgebraicGeometry.Spec (.of k)))
          (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange a T t Z p ∧ SpaceMapIsEtale Z T p ∧ SpaceMapIsSurjective Z T p

/-- Properness of the diagonal, in its scheme-test form for a DM stack. For every
pair of scheme maps the actual 2-fibre product is represented by `R`, and its map
`R → T ×_S U` is proper. The two projection comparisons lie over identity base maps;
an arbitrary equivalence or an unrelated proper morphism does not suffice.
For a DM stack this is precisely separatedness: a proper unramified algebraic-space
morphism is finite and representable by schemes, and properness is local on the target.
Source: Stacks Project, stacks-morphisms.tex, Definition `definition-separated`;
spaces-more-morphisms.tex, Lemma `lemma-characterize-finite`, and
spaces-morphisms.tex, Lemma `lemma-locally-quasi-finite-separated-representable`
(blueprint: def-sfb-moduli-stack-properties). -/
def HasProperModuliDiagonal {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ∀ (T U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
      (b : BasedFunctor (discreteModuli (yoneda.obj U)) F),
    ∃ (R : Over S) (p : R ⟶ T) (q : R ⟶ U)
        (e : BasedFunctor (discreteModuli (yoneda.obj R)) (moduliTwoFiberProduct a b)),
      e.toFunctor.IsEquivalence ∧ AlgebraicGeometry.IsProper (prod.lift p q).left ∧
      Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst a b))
        (discreteModuliMap (yoneda.map p))) ∧
      ∃ η : e.toFunctor ⋙ ObjectProperty.ι _ ⋙ Comma.snd a.toFunctor b.toFunctor ≅
          (discreteModuliMap (yoneda.map q)).toFunctor,
        ∀ x : (discreteModuli (yoneda.obj R)).obj,
          (discreteModuli (yoneda.obj U)).p.IsHomLift
            (𝟙 ((discreteModuli (yoneda.obj R)).p.obj x)) (η.hom.app x)

end CategoryTheory
