/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Sheaf.CategoryTheory.ModuleSheafificationRestriction
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import Mathlib.Algebra.Homology.ModelCategory.Injective
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

/-! # Derived functions on a free representable module

Source: Stacks Project, sites-cohomology.tex, Tags 08J7 and 03FD;
sites-modules.tex, Tag 03EM; derived.tex, Tag 015E.
(blueprint: lem-sfb-free-representable-derived-functions-model).

## Main definitions

* `free`, `hom`, `precomp`: the node's underived constructions.
* `leftComplex`, `rightComplex`: its specified injective-resolution derived models.
* `comparisonMap`: generator evaluation followed by an augmented resolution comparison.
* `unboundedComparison`: the same isomorphism under the inclusion into D.

## Main statements

* `free_representable_derived_functions_model`: the canonical comparison, with
  generator normalization and naturality in both arguments.
-/

@[expose] public section

set_option autoImplicit false

universe u wA

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FreeRepresentableDerivedFunctions

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u})

/-- The underlying ring sheaf. Source: Stacks 03EM.
(blueprint: lem-sfb-free-representable-derived-functions-model). -/
abbrev ring := (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R

/-- Ordinary module sheaves, using the recorded general ringed-site category.
Source: Stacks 03DA (blueprint: lem-sfb-free-representable-derived-functions-model). -/
abbrev modules := ringedSiteModules.{u} (ring J R)

/-- The free representable module functor, with its actual sheafification data.
Source: Stacks 03CY and 03DI
(blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def free : C ⥤ modules J R :=
  yoneda ⋙ PresheafOfModules.free (ring J R).obj ⋙
    PresheafOfModules.sheafification (𝟙 (ring J R).obj)

/-- The universal generator indexed by `b : W ⟶ P`, mapped through sheafification.
Source: Stacks 03CY and 03DI
(blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def generator (P W : C) (b : W ⟶ P) :
    ((free J R).obj P).val.obj (op W) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ring J R).obj)).unit.app
    ((PresheafOfModules.free (ring J R).obj).obj (yoneda.obj P))).app (op W)
      (ModuleCat.freeMk b)

/-- Internal Hom out of the free representable, using the recorded slice sheaf Hom.
Source: Stacks 03EM and 08J7
(blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def hom (P : C) : modules J R ⥤ modules J R :=
  (SheafOfModules.homFunctor R).obj (op ((free J R).obj P))

/-- Additivity is inherited from the existing tensor-Hom right adjunction.
Source: Stacks 03EM (blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable instance homAdditive (P : C) : (hom J R P).Additive :=
  letI : (hom J R P).IsRightAdjoint :=
    (SheafOfModules.tensorHomAdjunction R ((free J R).obj P)).isRightAdjoint
  Functor.additive_of_preserves_binary_products (hom J R P)

/-- Module injectives exist by the Grothendieck theorem; this installs the existing proof.
Source: Stacks 079H and 03DA
(blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable instance modulesEnoughInjectives : EnoughInjectives (modules J R) :=
  letI := SheafOfModules.isGrothendieckAbelianOfUniverses (J := J) (ring J R)
  IsGrothendieckAbelian.enoughInjectives

variable [HasFiniteProducts C]

/-- Exact precomposition on abelian presheaves by `V ↦ V × P`.
Source: Stacks 03EM (blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def precomp (P : C) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringLeft _ _ _).obj (prod.functor.flip.obj P).op

/-- Precomposition is additive, inherited from whiskering.
Source: Stacks 03EM (blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable instance precompAdditive (P : C) : (precomp P).Additive :=
  inferInstanceAs (((Functor.whiskeringLeft _ _ _).obj
    (prod.functor.flip.obj P).op).Additive)

/-- Precomposition preserves finite limits, computed at `V × P`.
Source: Stacks 03EM (blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable instance precompLimits (P : C) : PreservesFiniteLimits (precomp P) :=
  inferInstanceAs (PreservesFiniteLimits ((Functor.whiskeringLeft _ _ _).obj
    (prod.functor.flip.obj P).op))

/-- Precomposition preserves finite colimits, computed at `V × P`.
Source: Stacks 03EM (blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable instance precompColimits (P : C) : PreservesFiniteColimits (precomp P) :=
  inferInstanceAs (PreservesFiniteColimits ((Functor.whiskeringLeft _ _ _).obj
    (prod.functor.flip.obj P).op))

/-- The functor `a t_P ι` on abelian sheaves.
Source: Stacks 03EM and 03CY
(blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def sections (P : C) : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  sheafToPresheaf J AddCommGrpCat.{u} ⋙ precomp P ⋙ presheafToSheaf J AddCommGrpCat.{u}

/-- Additivity of the sectionwise sheafification construction.
Source: Stacks 03EM (blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable instance sectionsAdditive (P : C) : (sections J P).Additive :=
  inferInstanceAs ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
    precomp P ⋙ presheafToSheaf J AddCommGrpCat.{u}).Additive)

/-- Internal Hom followed by forgetting scalars.
Source: Stacks 08J7 and 03FD
(blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def homAbelian (P : C) : modules J R ⥤ Sheaf J AddCommGrpCat.{u} :=
  hom J R P ⋙ SheafOfModules.toSheaf (ring J R)

/-- Additivity of the underlying abelian internal Hom.
Source: Stacks 03EM (blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable instance homAbelianAdditive (P : C) : (homAbelian J R P).Additive :=
  inferInstanceAs ((hom J R P ⋙ SheafOfModules.toSheaf (ring J R)).Additive)

/-- The nonnegative representative of `D(U) RH_P(M[0])`: apply the actual sheaf Hom
and U to a nonnegative module-injective resolution, exactly as prescribed in the node.
Source: Stacks 08J7 (blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def leftComplex (P : C) {M : modules J R} (I : InjectiveResolution M) :
    CochainComplex.Plus (Sheaf J AddCommGrpCat.{u}) :=
  ⟨((homAbelian J R P).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex,
    0, inferInstance⟩

/-- The nonnegative representative of `D(a) D(t_P) Rι(A[0])`: apply ι to an
abelian-injective resolution of A, then the exact functors t_P and a.
Source: Stacks 03FD and 015E
(blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def rightComplex (P : C) {A : Sheaf J AddCommGrpCat.{u}}
    (T : InjectiveResolution A) : CochainComplex.Plus (Sheaf J AddCommGrpCat.{u}) :=
  ⟨((sections J P).mapHomologicalComplex (.up ℤ)).obj T.cochainComplex,
    0, inferInstance⟩

/-- Compatibility of a comparison from the underlying module resolution to the
abelian resolution with the identity augmentation of UM. This fixes the comparison
on degree zero and determines it up to homotopy.
Source: Stacks 013P and 013S
(blueprint: lem-sfb-free-representable-derived-functions-model). -/
def Compatible {M : modules J R} (I : InjectiveResolution M)
    (T : InjectiveResolution ((SheafOfModules.toSheaf (ring J R)).obj M))
    (c : ((SheafOfModules.toSheaf (ring J R)).mapHomologicalComplex (.up ℤ)).obj
      I.cochainComplex ⟶ T.cochainComplex) : Prop :=
  ((SheafOfModules.toSheaf (ring J R)).mapHomologicalComplex (.up ℤ)).map I.ι' ≫ c =
    (HomologicalComplex.singleMapHomologicalComplex
      (SheafOfModules.toSheaf (ring J R)) (.up ℤ) 0).hom.app M ≫ T.ι'

/-- Sheafify the generator-evaluation isomorphism, using the sheafification counit.
Source: Stacks 03EM and 03CY
(blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def sheafEvaluationIso (P : C)
    (θ : homAbelian J R P ⋙ sheafToPresheaf J AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf (ring J R) ⋙ sheafToPresheaf J AddCommGrpCat.{u} ⋙ precomp P) :
    homAbelian J R P ≅ SheafOfModules.toSheaf (ring J R) ⋙ sections J P :=
  (homAbelian J R P).rightUnitor.symm ≪≫
    Functor.isoWhiskerLeft (homAbelian J R P)
      (asIso (sheafificationAdjunction J AddCommGrpCat.{u}).counit).symm ≪≫
    Functor.isoWhiskerRight θ (presheafToSheaf J AddCommGrpCat.{u})

/-- The actual comparison of representative complexes: evaluate on generators,
then apply `a t_P ι` to the augmentation-compatible comparison c. No choice is made.
Source: Stacks 03EM, 03FD and 015E
(blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def comparisonMap (P : C)
    (θ : homAbelian J R P ⋙ sheafToPresheaf J AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf (ring J R) ⋙ sheafToPresheaf J AddCommGrpCat.{u} ⋙ precomp P)
    {M : modules J R} (I : InjectiveResolution M)
    (T : InjectiveResolution ((SheafOfModules.toSheaf (ring J R)).obj M))
    (c : ((SheafOfModules.toSheaf (ring J R)).mapHomologicalComplex (.up ℤ)).obj
      I.cochainComplex ⟶ T.cochainComplex) : leftComplex J R P I ⟶ rightComplex J P T :=
  ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex (sheafEvaluationIso J R P θ).hom (.up ℤ)).app
        I.cochainComplex ≫
      (Functor.mapHomologicalComplexCompIso
        (F := SheafOfModules.toSheaf (ring J R)) (G := sections J P)
        (Iso.refl (SheafOfModules.toSheaf (ring J R) ⋙ sections J P)) (.up ℤ)).inv.app
          I.cochainComplex ≫
      ((sections J P).mapHomologicalComplex (.up ℤ)).map c)

/-- The coefficient morphism on the internal-Hom representative.
Source: Stacks 08J7 (blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def leftMap (P : C) {M N : modules J R} {f : M ⟶ N}
    {I : InjectiveResolution M} {I' : InjectiveResolution N} (s : I.Hom I' f) :
    leftComplex J R P I ⟶ leftComplex J R P I' :=
  ObjectProperty.homMk (((homAbelian J R P).mapHomologicalComplex (.up ℤ)).map s.hom')

/-- The coefficient morphism on the derived-presheaf representative.
Source: Stacks 03FD (blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def rightMap (P : C) {A B : Sheaf J AddCommGrpCat.{u}} {f : A ⟶ B}
    {T : InjectiveResolution A} {T' : InjectiveResolution B} (t : T.Hom T' f) :
    rightComplex J P T ⟶ rightComplex J P T' :=
  ObjectProperty.homMk (((sections J P).mapHomologicalComplex (.up ℤ)).map t.hom')

/-- The parameter morphism on internal Hom is precomposition by the free-module map.
Source: Stacks 03EM (blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def leftParameterMap {P' P : C} (f : P' ⟶ P)
    {M : modules J R} (I : InjectiveResolution M) :
    leftComplex J R P I ⟶ leftComplex J R P' I :=
  let τ : homAbelian J R P ⟶ homAbelian J R P' :=
    Functor.whiskerRight ((SheafOfModules.homFunctor R).map ((free J R).map f).op)
      (SheafOfModules.toSheaf (ring J R))
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app I.cochainComplex)

/-- Restriction of presheaves along `1 × f`.
Source: Stacks 03EM (blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def precompParameterMap {P' P : C} (f : P' ⟶ P) : precomp P ⟶ precomp P' :=
  (Functor.whiskeringLeft Cᵒᵖ Cᵒᵖ AddCommGrpCat.{u}).map (NatTrans.op (prod.functor.flip.map f))

/-- The parameter morphism on the derived-presheaf representative is restriction
along `1 × f` followed by sheafification.
Source: Stacks 03EM and 015F
(blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def rightParameterMap {P' P : C} (f : P' ⟶ P)
    {A : Sheaf J AddCommGrpCat.{u}} (T : InjectiveResolution A) :
    rightComplex J P T ⟶ rightComplex J P' T :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat.{u})
      (Functor.whiskerRight (precompParameterMap f) (presheafToSheaf J AddCommGrpCat.{u})))
    (.up ℤ)).app T.cochainComplex)

variable [HasDerivedCategory.{wA} (Sheaf J AddCommGrpCat.{u})]

/-- The canonical isomorphism `D(U) RH_P(M[0]) ≅ D(a) D(t_P) Rι(UM[0])`,
written on the nonnegative injective representatives stipulated by the node.
The comparison is independent of all resolution and lifting choices, natural in
module maps and contravariantly in P, and normalized by evaluation on generators.
Source: Stacks sites-cohomology.tex, 08J7 and 03FD; sites-modules.tex, 03EM;
derived.tex, 015E (blueprint: lem-sfb-free-representable-derived-functions-model).

Proof: (1) The Grothendieck categories Mod(R), Ab and PAb have enough injectives;
choose nonnegative resolutions I of M and T of UM. (2) Restrict module
sheafification to C/V by lem-weil-pbc-module-sheafification-restriction; the free
module becomes free on (V × P -> V). (3) Apply the sheafification adjunction and
lem-weil-pbc-free-yoneda-presheaf-module in C/V. Evaluation on e_prP gives θ;
the inverse sends e_b over (W -> V) to restriction along (a,b). This proves
restriction and coefficient naturality as well as the displayed generator formula.
(4) U, a and t_P are exact, H_P is left exact, and both displayed complexes are
exactly the node's derived objects on these resolutions, by
lem-weil-pbc-exact-functor-derived-factorization and
lem-weil-pbc-right-derived-plus-injective. (5) The underlying abelian sheaf of a
module injective is ι-acyclic by lem-sc-injective-module-abelian-acyclic-zariski:
H^q(W,UI)=0 for q>0 (03FD). This does not assert UI is injective.
(6) Lift the abelian resolution augmentation along U(I)'s monomorphic
quasi-isomorphism by lem-weil-pbc-lift-along-injective-quasi-iso. It gives c with
Compatible I T c. The acyclic-complex comparison sk-thm-acyclicity implies ι(c)
is a quasi-isomorphism. (7) Apply θ termwise, then exact t_P and a. The resulting
comparisonMap is a quasi-isomorphism, hence gives E in D+.
(8) Two compatible c's are homotopic by
lem-weil-pbc-lift-to-injective-unique-up-to-homotopy. For coefficient maps, the
two routes to the target injective resolution lift the same augmented morphism,
so they are homotopic; all additive functors preserve these homotopies. This
proves the normalization for every c, independence of resolutions (take f=id),
and coefficient naturality. (9) The same resolutions for P and P' give parameter
naturality by restriction along 1 × f. On degree-zero kernels Compatible identifies
the comparison with θ and thus with generator evaluation. Applying the canonical
full inclusion D+ -> D gives the same comparison in the unbounded category. -/
theorem free_representable_derived_functions_model [J.Subcanonical] :
    ∃ (θ : ∀ P : C, homAbelian J R P ⋙ sheafToPresheaf J AddCommGrpCat.{u} ≅
        SheafOfModules.toSheaf (ring J R) ⋙ sheafToPresheaf J AddCommGrpCat.{u} ⋙ precomp P)
      (E : ∀ (P : C) (M : modules J R) (I : InjectiveResolution M)
        (T : InjectiveResolution ((SheafOfModules.toSheaf (ring J R)).obj M)),
        DerivedCategory.Plus.Q.obj (leftComplex J R P I) ≅
          DerivedCategory.Plus.Q.obj (rightComplex J P T)),
      (∀ (P V : C) (M : modules J R)
        (φ : (SheafOfModules.homObj (R := R) ((free J R).obj P) M).val.obj (op V)),
        ((θ P).hom.app M).app (op V) φ =
          φ.app (op (Over.mk (prod.fst : V ⨯ P ⟶ V)))
            (generator J R P (V ⨯ P) prod.snd)) ∧
      (∀ (M : modules J R) (I : InjectiveResolution M)
        (T : InjectiveResolution ((SheafOfModules.toSheaf (ring J R)).obj M)),
        ∃ c, Compatible J R I T c) ∧
      (∀ (P : C) (M : modules J R) (I : InjectiveResolution M)
        (T : InjectiveResolution ((SheafOfModules.toSheaf (ring J R)).obj M))
        (c : ((SheafOfModules.toSheaf (ring J R)).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex ⟶ T.cochainComplex),
        Compatible J R I T c → (E P M I T).hom =
          DerivedCategory.Plus.Q.map (comparisonMap J R P (θ P) I T c)) ∧
      (∀ (P : C) (M N : modules J R) (f : M ⟶ N)
        (I : InjectiveResolution M) (I' : InjectiveResolution N)
        (T : InjectiveResolution ((SheafOfModules.toSheaf (ring J R)).obj M))
        (T' : InjectiveResolution ((SheafOfModules.toSheaf (ring J R)).obj N))
        (s : I.Hom I' f) (t : T.Hom T' ((SheafOfModules.toSheaf (ring J R)).map f)),
        DerivedCategory.Plus.Q.map (leftMap J R P s) ≫ (E P N I' T').hom =
          (E P M I T).hom ≫ DerivedCategory.Plus.Q.map (rightMap J P t)) ∧
      (∀ (P' P : C) (f : P' ⟶ P) (M : modules J R) (I : InjectiveResolution M)
        (T : InjectiveResolution ((SheafOfModules.toSheaf (ring J R)).obj M)),
        DerivedCategory.Plus.Q.map (leftParameterMap J R f I) ≫ (E P' M I T).hom =
          (E P M I T).hom ≫ DerivedCategory.Plus.Q.map (rightParameterMap J f T)) := by
  sorry

/-- Send the comparison between the bounded-below derived representatives to the
ordinary unbounded derived category using its canonical full inclusion.
Source: Stacks 08J7 (blueprint: lem-sfb-free-representable-derived-functions-model). -/
noncomputable def unboundedComparison {P : C} {M : modules J R}
    {I : InjectiveResolution M}
    {T : InjectiveResolution ((SheafOfModules.toSheaf (ring J R)).obj M)}
    (E : DerivedCategory.Plus.Q.obj (leftComplex J R P I) ≅
      DerivedCategory.Plus.Q.obj (rightComplex J P T)) :
    DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj (leftComplex J R P I)) ≅
      DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj (rightComplex J P T)) :=
  DerivedCategory.Plus.ι.mapIso E

end CategoryTheory.FreeRepresentableDerivedFunctions
