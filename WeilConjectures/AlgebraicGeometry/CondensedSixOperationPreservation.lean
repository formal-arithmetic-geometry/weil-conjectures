/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.SixFunctors.IntegralRestrictionBoundedDescent
import WeilConjectures.AlgebraicGeometry.FiniteConstantStratifiedZariskiLocality
import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.LocalizingClosureExistence
import WeilConjectures.AlgebraicGeometry.ExceptionalInverseImageExistence
import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.CompactlyGenerated
import WeilConjectures.AlgebraicGeometry.MateOpenProperSupport
import WeilConjectures.AlgebraicGeometry.CondensedSupportDerivedLocalization
import WeilConjectures.CategoryTheory.BrownRepresentabilityRightAdjoint
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Six-operation preservation without separatedness of the schemes

Source: latest blueprint, sec-poincare-duality/sk-thm-frobenius,
prop-weil-operations.proof.md, first sentence, and sec-six-functors-basics,
sk-thm-sf-ctf-stability (blueprint: lem-pod-condensed-six-operation-preservation).

The exceptional adjunction lives on the ordinary localizing closures. Its constructible
restriction is normalized by the original Hom equivalences, hence by the original units
and counits. The schemes themselves need not be separated over the base field.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

/-- The two functors preserve the indicated full subcategories and their adjunction
restricts with exactly the original Hom equivalences. Taking identity morphisms in
these equivalences recovers the original unit and counit components. This predicate
records the normalization clause, using `ObjectProperty.lift` for the actual restrictions;
it does not choose any functor or adjunction.

Source: latest blueprint sk-thm-sf-ctf-stability, last sentence, and the node's step 12
(blueprint: lem-pod-condensed-six-operation-preservation). -/
def RestrictsWithOriginalHomEquiv
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (P : ObjectProperty C) (Q : ObjectProperty D) : Prop :=
  ∃ (hF : ∀ K : P.FullSubcategory, Q (F.obj K.obj))
    (hG : ∀ N : Q.FullSubcategory, P (G.obj N.obj)),
    ∃ restricted : Q.lift (P.ι ⋙ F) hF ⊣ P.lift (Q.ι ⋙ G) hG,
      ∀ (K : P.FullSubcategory) (N : Q.FullSubcategory)
        (a : (Q.lift (P.ι ⋙ F) hF).obj K ⟶ N),
        (restricted.homEquiv K N a).hom = adj.homEquiv K.obj N.obj a.hom

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The six condensed operations preserve bounded constructible complexes on arbitrary
finite-type schemes, and all three adjunctions retain their original units and counits.

Source: latest blueprint prop-weil-operations.proof.md, first sentence, invoking
sk-thm-sf-ctf-stability, with the nonseparated scheme scope specified by the DAG node
(blueprint: lem-pod-condensed-six-operation-preservation).

Proof plan (the node's twelve steps):
1. Finite-type schemes over a field are Noetherian and qcqs. Choose finite affine
   covers of the targets. The source over each affine chart is separated of finite
   type, because the morphism is separated; intersections are again qc separated opens.
2. Boundedness descends along finite open covers (lem-int-restriction-bounded-descent),
   as does constant-model constructibility (lem-sfb-constructible-zariski-locality).
   For the field coefficients lem-integral-ctf-equals-bc identifies Dbc with Dctf.
   Exact open extension preserves both boundedness and the finite stratum models.
3. Open restriction and extension preserve localizing closures. The two-open
   Mayer--Vietoris triangle of lem-pod-condensed-open-derived-calculus and induction
   give finite-cover locality of these closures. Restrictions jointly detect zero
   objects and isomorphisms, by cohomology and sheaf gluing.
4. Apply sk-thm-existence on affine charts, using finite ell-cohomological dimension.
   Extend its small compact generators by zero. Open adjunction and preservation of
   coproducts prove compactness; joint detection proves generation globally.
5. Open comparison for pullback, direct image, tensor and internal Hom reduces their
   preservation to sk-thm-sf-ctf-stability on the separated affine charts. Descend
   constructibility and the finitely many cohomological bounds using step 2.
6. Nagata supplies a compactification. Its lower shriek is Rp_* D(j_!). On each
   affine target chart sk-thm-existence makes it exact, coproduct preserving and
   constructible preserving. Chart detection and minimality of the localizing
   closure give preservation of the global localizing closures.
7. For a proper map and a target open, transpose the open restriction comparison.
   Its open restriction is invertible. The affine-chart support calculation of
   lem-sfb-mate-open-proper-support makes its closed restriction zero. The open/closed
   detection of lem-sfb-condensed-support-derived-localization makes it invertible.
8. Combine step 7 with composition of open extensions to obtain F u_! = v_! F_i,
   normalized as the transpose of the actual open comparison.
9. Brown representability on the compactly generated closures gives F adjoint to G.
   Transport integer shifts through the adjunction; the shift-compatible right
   adjoint is triangulated (lem-sf-triangulated-right-adjoint).
10. The chain Hom(A,u^*GN) = Hom(u_!A,GN) = Hom(Fu_!A,N)
    = Hom(v_!F_iA,N) = Hom(F_iA,v^*N) = Hom(A,G_i v^*N)
    gives u^*G = G_i v^* by Yoneda, with the original adjunction normalizations.
11. Local exceptional preservation from sk-thm-existence and finite-cover descent
    give constructible preservation of G. In the separated case uniqueness of right
    adjoints identifies it, counit compatibly, with sk-prop-sf-existence's adjoint.
12. Full inclusions change no Hom sets. Restrict the original three Hom bijections;
    this retains the original units and counits, completing every clause.
-/
theorem condensedSixOperationPreservation
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (_hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ℓ k)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    (∀ (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom] [QuasiCompact T.hom],
      (boundedConstructible (condensedRingObj Λ T.left) =
        constantModelBoundedConstructible Λ T.left ⊓
          fun K ↦ DerivedCategory.finiteTorAmplitude _ K) ∧
      (∀ K : BoundedConstructible (condensedRingObj Λ T.left),
        (derivedTensorHomAdjunction Λ K.obj).RestrictsWithOriginalHomEquiv
          (boundedConstructible (condensedRingObj Λ T.left))
          (boundedConstructible (condensedRingObj Λ T.left)))) ∧
    (∀ (X Y : Over (Spec (.of k)))
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      (f : X ⟶ Y) [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      [IsSeparated f.left],
      (derivedUpperStarLowerStarAdjunction Λ f.left).RestrictsWithOriginalHomEquiv
        (boundedConstructible (condensedRingObj Λ Y.left))
        (boundedConstructible (condensedRingObj Λ X.left)) ∧
      Nonempty (Compactification f.left) ∧
      ∀ c : Compactification f.left,
        ∃ (h : ∀ K, localizingClosureProEtale Λ X.left K →
            localizingClosureProEtale Λ Y.left
              ((rightDerivedLowerShriekOfCompactification Λ c).obj K))
          (_hCX : boundedConstructible (condensedRingObj Λ X.left) ≤
            localizingClosureProEtale Λ X.left)
          (_hCY : boundedConstructible (condensedRingObj Λ Y.left) ≤
            localizingClosureProEtale Λ Y.left)
          (hX : (localizingClosureProEtale Λ X.left).IsTriangulated)
          (hY : (localizingClosureProEtale Λ Y.left).IsTriangulated),
          (fun [triX : (localizingClosureProEtale Λ X.left).IsTriangulated]
              [triY : (localizingClosureProEtale Λ Y.left).IsTriangulated] ↦
            ∃ G : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
                (localizingClosureProEtale Λ X.left).FullSubcategory,
              ∃ s : G.CommShift ℤ,
                (fun [comm : G.CommShift ℤ] ↦
                  G.IsTriangulated ∧
                  ∃ adj : localizingLowerShriek Λ c h ⊣ G,
                    adj.RestrictsWithOriginalHomEquiv
                      (fun K ↦ boundedConstructible (condensedRingObj Λ X.left) K.obj)
                      (fun N ↦ boundedConstructible (condensedRingObj Λ Y.left) N.obj) ∧
                    (∀ (J : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
                        (localizingClosureProEtale Λ X.left).FullSubcategory)
                      (adjJ : localizingLowerShriek Λ c h ⊣ J),
                      ∃! e : G ≅ J, ∀ N,
                        (localizingLowerShriek Λ c h).map (e.hom.app N) ≫
                          adjJ.counit.app N = adj.counit.app N))
                  (comm := s))
            (triX := hX) (triY := hY)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
