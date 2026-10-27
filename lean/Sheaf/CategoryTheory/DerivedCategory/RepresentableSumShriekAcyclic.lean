/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import Mathlib.Algebra.DirectSum.Module
import Sheaf.CategoryTheory.DerivedCategory.BoundedAboveAcyclicComputation

/-! # Representable sums and left-Kan acyclicity

Source: Stacks Project, Cohomology on Sites, Tag 08PG, with the arbitrary-coefficient
projective-resolution refinement in the DAG proof
(blueprint: lem-trf-representable-sum-shriek-acyclic).

`evaluationLeftAdjoint (ModuleCat R) (op U)` is the existing construction of `L_U`:
its value at `op V` is the coproduct indexed by `op U ⟶ op V`, hence by `V ⟶ U`.
Its coproduct maps are the finite-support direct-sum maps of modules. We use the
presheaf category itself, as the node explicitly does: identity coverings impose
no extra sheaf condition on a module presheaf. `colim` is over the opposite category,
and `u.op.lan` is the left adjoint to precomposition. No topology or site structure
is required on `u`.
-/

@[expose] public section

set_option autoImplicit false

universe u wE wD wR

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable (E : Type u) [SmallCategory E] (R : Type u) [CommRing R]

/-- The restriction and evaluation formulas for the existing representable copower.
Source: Stacks Project, Tag 08PG, representable generators
(blueprint: lem-trf-representable-sum-shriek-acyclic).

Proof (steps 1 and 3): coproducts of modules are finite-support direct sums.
Restriction sends the summand `a` to `a ≫ b` in the opposite category.
Evaluate a natural transformation on the identity summand. Naturality forces its
value on `a` to be restriction of that value; conversely these formulas give a
natural transformation by the coproduct universal property. The two constructions
are inverse and commute with maps of the coefficient module and of the presheaf,
as expressed by Mathlib's evaluation adjunction. -/
theorem representableModule_formulas (U : E) (M : ModuleCat.{u} R) :
    (∀ (V W : Eᵒᵖ) (a : op U ⟶ V) (b : V ⟶ W),
      Sigma.ι (fun _ : op U ⟶ V ↦ M) a ≫
          ((evaluationLeftAdjoint (ModuleCat.{u} R) (op U)).obj M).map b =
        Sigma.ι (fun _ : op U ⟶ W ↦ M) (a ≫ b)) ∧
    (∀ (H : Eᵒᵖ ⥤ ModuleCat.{u} R)
      (θ : (evaluationLeftAdjoint (ModuleCat.{u} R) (op U)).obj M ⟶ H),
      (evaluationAdjunctionRight (ModuleCat.{u} R) (op U)).homEquiv M H θ =
        Sigma.ι (fun _ : op U ⟶ op U ↦ M) (𝟙 (op U)) ≫ θ.app (op U)) ∧
    (∀ (H : Eᵒᵖ ⥤ ModuleCat.{u} R) (f : M ⟶ H.obj (op U))
      (V : Eᵒᵖ) (a : op U ⟶ V),
      Sigma.ι (fun _ : op U ⟶ V ↦ M) a ≫
          (((evaluationAdjunctionRight (ModuleCat.{u} R) (op U)).homEquiv M H).symm f).app V =
        f ≫ H.map a) := by
  sorry

/-- Exactness and projectivity of representable copowers, with the specified generator epi.
Source: Stacks Project, Tag 08PG, representable generators and finite-support refinement
(blueprint: lem-trf-representable-sum-shriek-acyclic).

Proof (steps 1--5): kernels and cokernels of module presheaves are pointwise, and
an epi is pointwise surjective. Small direct sums preserve short exact sequences:
lift only the finitely many nonzero coordinates. Thus each `L_U` is exact.
A map out of `L_U(P)` is a map out of `P` into the evaluation at `U`; lift it
across a pointwise epi and use the evaluation adjunction. Sums of projectives are
projective by choosing a lift on each summand. The module `R` is projective since
a map from it is determined by the image of 1. The indicated generator map sends
`(a,r)` in the summand `(U,x)` to `r • H(a)(x)`. Every `y : H(V)` lifts using
`(V,y)`, the identity arrow and coefficient 1. The analogous free module epi
supplies enough projectives for modules. These observations prove all conjuncts. -/
theorem representableModule_exact_projective_generators :
    (∀ U : E,
      PreservesFiniteLimits (evaluationLeftAdjoint (ModuleCat.{u} R) (op U)) ∧
      PreservesFiniteColimits (evaluationLeftAdjoint (ModuleCat.{u} R) (op U))) ∧
    (∀ (U : E) (P : ModuleCat.{u} R), Projective P →
      Projective ((evaluationLeftAdjoint (ModuleCat.{u} R) (op U)).obj P)) ∧
    EnoughProjectives (ModuleCat.{u} R) ∧ EnoughProjectives (Eᵒᵖ ⥤ ModuleCat.{u} R) ∧
    (∀ H : Eᵒᵖ ⥤ ModuleCat.{u} R,
      Projective (∐ fun p : Σ U : E, H.obj (op U) ↦
        (evaluationLeftAdjoint (ModuleCat.{u} R) (op p.1)).obj (ModuleCat.of R R)) ∧
      Epi (Sigma.desc fun p : Σ U : E, H.obj (op U) ↦
        ((evaluationAdjunctionRight (ModuleCat.{u} R) (op p.1)).homEquiv
          (ModuleCat.of R R) H).symm
            (ModuleCat.ofHom (LinearMap.toSpanSingleton R (H.obj (op p.1)) p.2)))) ∧
    (∀ (I : Type u) (P : I → ModuleCat.{u} R),
      (∀ i : I, Projective (P i)) → Projective (∐ P)) ∧
    (∀ (I : Type u) (P : I → Eᵒᵖ ⥤ ModuleCat.{u} R),
      (∀ i : I, Projective (P i)) → Projective (∐ P)) := by
  sorry

/-- The representable copower, colimit and left Kan functors are additive.
Source: Stacks Project, Tag 08PG, pointwise sums and the two left adjunctions
(blueprint: lem-trf-representable-sum-shriek-acyclic).

Proof (steps 2 and 8): coefficient maps of a copower are sums of the same map,
so preserve addition. Colimit and left Kan extension preserve zero and finite
coproducts as left adjoints. In additive categories, addition is the composite
of diagonal, direct sum of maps and codiagonal. Preservation of these maps
proves additivity, without any exactness assumption on the functor `u`. -/
theorem representableModule_additive (D : Type u) [SmallCategory D] (u : E ⥤ D) :
    (∀ U : E, (evaluationLeftAdjoint (ModuleCat.{u} R) (op U)).Additive) ∧
    (colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).Additive ∧
    (u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R)).Additive := by
  sorry

/-- The additive structure of the already constructed representable copower.
Source: Stacks Project, Tag 08PG (blueprint: lem-trf-representable-sum-shriek-acyclic). -/
instance representableModule_additive_instance (U : E) :
    (evaluationLeftAdjoint (ModuleCat.{u} R) (op U)).Additive :=
  (representableModule_additive E R E (𝟭 E)).1 U

/-- The additive structure of the existing colimit functor.
Source: Stacks Project, Tag 08PG (blueprint: lem-trf-representable-sum-shriek-acyclic). -/
instance modulePresheaf_colim_additive :
    (colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).Additive :=
  (representableModule_additive E R E (𝟭 E)).2.1

/-- The additive structure of the existing left Kan extension functor.
Source: Stacks Project, Tag 08PG (blueprint: lem-trf-representable-sum-shriek-acyclic). -/
instance modulePresheaf_lan_additive (D : Type u) [SmallCategory D] (u : E ⥤ D) :
    (u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R)).Additive :=
  (representableModule_additive E R D u).2.2

/-- Exactness of small sums in modules and module presheaves.
Source: Stacks Project, Tag 08PG, finite-support refinement
(blueprint: lem-trf-representable-sum-shriek-acyclic).

Proof (steps 1--2): injectivity of the direct sum of injections holds on each
coordinate. For kernel exactness and surjectivity choose preimages in the finitely
many nonzero coordinates. This proves module exactness; evaluate at each object
to obtain presheaf exactness. The empty family is the zero short exact sequence. -/
theorem modulePresheaf_smallSums_exact (I : Type u) :
    (∀ S : ShortComplex (Discrete I ⥤ ModuleCat.{u} R),
      (∀ i : I, (S.map ((evaluation (Discrete I) (ModuleCat.{u} R)).obj ⟨i⟩)).ShortExact) →
        (S.map (colim : (Discrete I ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R)).ShortExact) ∧
    (∀ S : ShortComplex (Discrete I ⥤ Eᵒᵖ ⥤ ModuleCat.{u} R),
      (∀ i : I, (S.map
        ((evaluation (Discrete I) (Eᵒᵖ ⥤ ModuleCat.{u} R)).obj ⟨i⟩)).ShortExact) →
        (S.map (colim : (Discrete I ⥤ Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤
          (Eᵒᵖ ⥤ ModuleCat.{u} R))).ShortExact) := by
  sorry

/-- The natural colimit and left-Kan identifications, normalized on every generator.
Source: Stacks Project, Tag 08PG, universal-property refinement
(blueprint: lem-trf-representable-sum-shriek-acyclic).

Proof (steps 6--8): the maps sending every `(a,m)` to `m` form a colimit cocone.
Every cocone factors uniquely through its identity summand at `U`, so this is a
colimit. For Kan extension, take the adjunct of `(a,m) ↦ (u(a),m)`. The reverse
map is determined by the identity summand and the adjunction unit. The evaluation
adjunction and naturality of the unit show both composites are identities.
Both formulas commute with coefficient maps, giving natural isomorphisms.
The normalization specifies the maps, rather than an arbitrary isomorphism. -/
theorem representableModule_colim_lan (D : Type u) [SmallCategory D] (u : E ⥤ D) (U : E) :
    (∃ e : evaluationLeftAdjoint (ModuleCat.{u} R) (op U) ⋙
        (colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R) ≅ 𝟭 (ModuleCat.{u} R),
      ∀ (M : ModuleCat.{u} R) (V : Eᵒᵖ) (a : op U ⟶ V),
        Sigma.ι (fun _ : op U ⟶ V ↦ M) a ≫
            colimit.ι ((evaluationLeftAdjoint (ModuleCat.{u} R) (op U)).obj M) V ≫
              e.hom.app M = 𝟙 M) ∧
    (∃ e : evaluationLeftAdjoint (ModuleCat.{u} R) (op U) ⋙ u.op.lan ≅
        evaluationLeftAdjoint (ModuleCat.{u} R) (op (u.obj U)),
      ∀ (M : ModuleCat.{u} R) (V : Eᵒᵖ) (a : op U ⟶ V),
        Sigma.ι (fun _ : op U ⟶ V ↦ M) a ≫
            ((u.op.lanAdjunction (ModuleCat.{u} R)).unit.app
              ((evaluationLeftAdjoint (ModuleCat.{u} R) (op U)).obj M)).app V ≫
            (e.hom.app M).app (u.op.obj V) =
          Sigma.ι (fun _ : op (u.obj U) ⟶ u.op.obj V ↦ M) (u.op.map a)) := by
  sorry

/-- Every small sum of representables with arbitrary coefficients is colimit-acyclic.
Source: Stacks Project, Tag 08PG and Derived Categories, Tags 0646, 05S8--05S9
(blueprint: lem-trf-representable-sum-shriek-acyclic).

Proof (steps 9--10): resolve each coefficient module by projectives in degrees at
most zero, using `exists_boundedAbove_projective_resolution`. Exactness of `L_U`
and of sums makes their sum a projective resolution of the indicated presheaf.
Colimit takes this resolution to the direct sum of the coefficient resolutions,
which still resolves the sum of coefficients. Projective computation in
`boundedAbove_acyclic_leftDerived_computation` makes the canonical comparison
invertible on this resolution. Naturality of the comparison at its augmentation
and the two quasi-isomorphisms make it invertible at the presheaf in degree zero.
No coefficient is assumed projective. -/
theorem representableModule_sum_colim_acyclic
    [HasDerivedCategory.{wE} (Eᵒᵖ ⥤ ModuleCat.{u} R)]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    (LC : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (ε : DerivedCategory.Q ⋙ LC ⟶
      (colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hLC : LC.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso (Eᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (hdefined : ∀ X : HomotopyCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ),
      ∃ Y : DerivedCategory (ModuleCat.{u} R), IsEssentiallyConstantProDiagram
        (MorphismProperty.Over.forget
          (HomotopyCategory.quasiIso (Eᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ)) ⊤ X ⋙
          Over.forget X ⋙
          (colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) Y)
    (I : Type u) (U : I → E) (M : I → ModuleCat.{u} R) :
    IsIso (ε.app ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj
      (∐ fun c : I ↦ (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U c))).obj (M c)))) := by
  sorry

/-- Left Kan extension takes a sum of representables to the sum on the image objects,
and that sum is left-Kan acyclic. The displayed unit normalization fixes the sum iso.
Source: Stacks Project, Tag 08PG and Derived Categories, Tags 0646, 05S8--05S9
(blueprint: lem-trf-representable-sum-shriek-acyclic).

Proof (steps 7--10): left Kan extension preserves coproducts, and its normalized
isomorphism on each representable therefore gives the normalized sum isomorphism.
For acyclicity, sum the induced coefficient projective resolutions as in the
colimit case. Its Kan image is the sum of induced resolutions on `D`, exact by
pointwise sums and exactness of each `L_{uU}`. The canonical comparison is invertible
on the source projective resolution by the bounded-above computation theorem.
Naturality at the augmentation, whose Kan image is also a quasi-isomorphism,
proves invertibility of the particular comparison in the conclusion. -/
theorem representableModule_sum_lan_acyclic
    (D : Type u) [SmallCategory D] (u : E ⥤ D)
    [HasDerivedCategory.{wE} (Eᵒᵖ ⥤ ModuleCat.{u} R)]
    [HasDerivedCategory.{wD} (Dᵒᵖ ⥤ ModuleCat.{u} R)]
    (LK : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤
      DerivedCategory (Dᵒᵖ ⥤ ModuleCat.{u} R))
    (ε : DerivedCategory.Q ⋙ LK ⟶
      (u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hLK : LK.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso (Eᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (hdefined : ∀ X : HomotopyCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ),
      ∃ Y : DerivedCategory (Dᵒᵖ ⥤ ModuleCat.{u} R), IsEssentiallyConstantProDiagram
        (MorphismProperty.Over.forget
          (HomotopyCategory.quasiIso (Eᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ)) ⊤ X ⋙
          Over.forget X ⋙
          (u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤
            (Dᵒᵖ ⥤ ModuleCat.{u} R)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) Y)
    (I : Type u) (U : I → E) (M : I → ModuleCat.{u} R) :
    IsIso (ε.app ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj
      (∐ fun c : I ↦ (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U c))).obj (M c)))) ∧
    (∃ e : u.op.lan.obj
        (∐ fun c : I ↦ (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U c))).obj (M c)) ≅
        ∐ fun c : I ↦
          (evaluationLeftAdjoint (ModuleCat.{u} R) (op (u.obj (U c)))).obj (M c),
      ∀ (c : I) (V : Eᵒᵖ) (a : op (U c) ⟶ V),
        Sigma.ι (fun _ : op (U c) ⟶ V ↦ M c) a ≫
            (Sigma.ι (fun j : I ↦
              (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U j))).obj (M j)) c).app V ≫
            ((u.op.lanAdjunction (ModuleCat.{u} R)).unit.app
              (∐ fun j : I ↦
                (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U j))).obj (M j))).app V ≫
            e.hom.app (u.op.obj V) =
          Sigma.ι (fun _ : op (u.obj (U c)) ⟶ u.op.obj V ↦ M c) (u.op.map a) ≫
            (Sigma.ι (fun j : I ↦
              (evaluationLeftAdjoint (ModuleCat.{u} R) (op (u.obj (U j)))).obj
                (M j)) c).app (u.op.obj V)) := by
  sorry

/-- The Kan image sum is also colimit-acyclic on the target category.
Source: Stacks Project, Tag 08PG and Derived Categories, Tags 0646, 05S8--05S9
(blueprint: lem-trf-representable-sum-shriek-acyclic).

Proof (step 10): the preceding normalized coproduct isomorphism identifies the
Kan image with the sum of `L_{uU_c}(M_c)`. Apply the colimit-acyclicity assertion
on `D` to that family. Naturality of the canonical comparison under this iso
transports invertibility to the Kan image itself. -/
theorem representableModule_sum_lan_colim_acyclic
    (D : Type u) [SmallCategory D] (u : E ⥤ D)
    [HasDerivedCategory.{wD} (Dᵒᵖ ⥤ ModuleCat.{u} R)]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    (LC : DerivedCategory (Dᵒᵖ ⥤ ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (ε : DerivedCategory.Q ⋙ LC ⟶
      (colim : (Dᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hLC : LC.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (hdefined : ∀ X : HomotopyCategory (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ),
      ∃ Y : DerivedCategory (ModuleCat.{u} R), IsEssentiallyConstantProDiagram
        (MorphismProperty.Over.forget
          (HomotopyCategory.quasiIso (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ)) ⊤ X ⋙
          Over.forget X ⋙
          (colim : (Dᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) Y)
    (I : Type u) (U : I → E) (M : I → ModuleCat.{u} R) :
    IsIso (ε.app ((CochainComplex.singleFunctor (Dᵒᵖ ⥤ ModuleCat.{u} R) 0).obj
      (u.op.lan.obj (∐ fun c : I ↦
        (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U c))).obj (M c))))) := by
  sorry

/-- The sum of the induced augmentations, with codomain the sum in degree zero.
Source: Stacks Project, Tag 08PG, arbitrary-coefficient refinement, proof step 9
(blueprint: lem-trf-representable-sum-shriek-acyclic).
This uses only functorial images, the standard single-complex comparison and
coproduct inclusions; no object or morphism is chosen from a postponed existence proof. -/
noncomputable def representableModule_resolutionAugmentation
    (I : Type u) (U : I → E) (M : I → ModuleCat.{u} R)
    (P : I → CochainComplex (ModuleCat.{u} R) ℤ)
    (a : ∀ c : I, P c ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (M c)) :
    (∐ fun c : I ↦
      ((evaluationLeftAdjoint (ModuleCat.{u} R) (op (U c))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (P c)) ⟶
    (CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj
      (∐ fun c : I ↦ (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U c))).obj (M c)) :=
  Sigma.desc fun c : I ↦
    ((evaluationLeftAdjoint (ModuleCat.{u} R) (op (U c))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (a c) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U c))) (ComplexShape.up ℤ) 0).hom.app
        (M c) ≫
    (CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).map
      (Sigma.ι (fun j : I ↦
        (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U j))).obj (M j)) c)

/-- The induced sum is a projective resolution, and its colimit and Kan images
resolve the corresponding sums in degree zero.
Source: Stacks Project, Tag 08PG and Derived Categories, Tag 0646
(blueprint: lem-trf-representable-sum-shriek-acyclic).

Proof (step 9): the projective coefficients remain projective under `L_U` and
under sums. The construction stays zero above degree zero. Exactness of `L_U`
and small sums shows that the displayed augmentation is a quasi-isomorphism.
The normalized colimit isos identify its colimit image with the sum of `a c`,
which is a quasi-isomorphism by exactness of sums of modules. The normalized Kan
isos identify its Kan image with the sum of the induced `a c` on `D`; exactness
of those copowers and sums again gives a quasi-isomorphism. The final two
isomorphisms express the respective degree-zero targets as the sums stated in
the node. These comparisons apply to every supplied resolution, not only a
chosen family. -/
theorem representableModule_sum_resolution
    (D : Type u) [SmallCategory D] (u : E ⥤ D)
    (I : Type u) (U : I → E) (M : I → ModuleCat.{u} R)
    (P : I → CochainComplex (ModuleCat.{u} R) ℤ)
    (a : ∀ c : I, P c ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (M c))
    (hP : ∀ c : I, (P c).IsStrictlyLE 0)
    (hprojective : ∀ (c : I) (n : ℤ), Projective ((P c).X n))
    (ha : ∀ c : I, QuasiIso (a c)) :
    CochainComplex.IsStrictlyLE (∐ fun c : I ↦
      ((evaluationLeftAdjoint (ModuleCat.{u} R) (op (U c))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (P c)) 0 ∧
    (∀ n : ℤ, Projective ((∐ fun c : I ↦
      ((evaluationLeftAdjoint (ModuleCat.{u} R) (op (U c))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (P c)).X n)) ∧
    QuasiIso (representableModule_resolutionAugmentation E R I U M P a) ∧
    QuasiIso ((colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomologicalComplex
      (ComplexShape.up ℤ) |>.map (representableModule_resolutionAugmentation E R I U M P a)) ∧
    QuasiIso ((u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤
      (Dᵒᵖ ⥤ ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.up ℤ) |>.map
        (representableModule_resolutionAugmentation E R I U M P a)) ∧
    (∃ e : (colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).obj
        (∐ fun c : I ↦ (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U c))).obj (M c)) ≅
          ∐ M,
      (∀ (c : I) (V : Eᵒᵖ) (b : op (U c) ⟶ V),
        Sigma.ι (fun _ : op (U c) ⟶ V ↦ M c) b ≫
            (Sigma.ι (fun j : I ↦
              (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U j))).obj (M j)) c).app V ≫
            colimit.ι (∐ fun j : I ↦
              (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U j))).obj (M j)) V ≫
            e.hom = Sigma.ι M c) ∧
      QuasiIso (((colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (representableModule_resolutionAugmentation E R I U M P a) ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R)
            (ComplexShape.up ℤ) 0).hom.app
              (∐ fun c : I ↦
                (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U c))).obj (M c)) ≫
        (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map e.hom)) ∧
    (∃ e : u.op.lan.obj
        (∐ fun c : I ↦ (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U c))).obj (M c)) ≅
          ∐ fun c : I ↦
            (evaluationLeftAdjoint (ModuleCat.{u} R) (op (u.obj (U c)))).obj (M c),
      (∀ (c : I) (V : Eᵒᵖ) (b : op (U c) ⟶ V),
        Sigma.ι (fun _ : op (U c) ⟶ V ↦ M c) b ≫
            (Sigma.ι (fun j : I ↦
              (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U j))).obj (M j)) c).app V ≫
            ((u.op.lanAdjunction (ModuleCat.{u} R)).unit.app
              (∐ fun j : I ↦
                (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U j))).obj (M j))).app V ≫
            e.hom.app (u.op.obj V) =
          Sigma.ι (fun _ : op (u.obj (U c)) ⟶ u.op.obj V ↦ M c) (u.op.map b) ≫
            (Sigma.ι (fun j : I ↦
              (evaluationLeftAdjoint (ModuleCat.{u} R) (op (u.obj (U j)))).obj
                (M j)) c).app (u.op.obj V)) ∧
      QuasiIso (((u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤
          (Dᵒᵖ ⥤ ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (representableModule_resolutionAugmentation E R I U M P a) ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R))
            (ComplexShape.up ℤ) 0).hom.app
              (∐ fun c : I ↦
                (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U c))).obj (M c)) ≫
        (CochainComplex.singleFunctor (Dᵒᵖ ⥤ ModuleCat.{u} R) 0).map e.hom)) := by
  sorry

end CategoryTheory
