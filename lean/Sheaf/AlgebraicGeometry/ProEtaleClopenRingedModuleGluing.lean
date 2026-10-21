/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Exact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.SiteModuleSheafGluing
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Module gluing on a finite clopen pro-etale partition

Source: Stacks Project, Tags 04TQ, 04TR and 04TS, finite-disjoint module expansion
(blueprint: lem-pur-clopen-ringed-module-gluing).

The restriction helpers below are the existing continuous pushforward constructions.
The gluing theorem specifies its inverse on sections, morphisms and restriction maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe t u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Restriction of ring sheaves along composition into a weakly etale open subscheme.
Source: Stacks Project, Tag 04TR (blueprint: lem-pur-clopen-ringed-module-gluing). -/
abbrev clopenRingRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j] :=
  (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).sheafPushforwardContinuous
    RingCat.{u} (topology Y) (topology X)

/-- Restriction of module sheaves, with the unchanged sectionwise scalar actions.
Source: Stacks Project, Tag 04TR (blueprint: lem-pur-clopen-ringed-module-gluing). -/
abbrev clopenModuleRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    ringedSiteModules.{v} R ⥤ ringedSiteModules.{v} ((clopenRingRestriction j).obj R) :=
  SheafOfModules.pushforward (F := MorphismProperty.Over.map ⊤
    (inferInstance : WeaklyEtale j)) (𝟙 _)

/-- The component of a test object, as an object of the component's own pro-etale site.
Source: Stacks Project, Tag 04TR (blueprint: lem-pur-clopen-ringed-module-gluing). -/
abbrev clopenTestPiece {X Y : Scheme.{t}} (j : Y ⟶ X) (U : X.ProEt) : Y.ProEt :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj U

/-- The component projection into the ambient test object.
Source: Stacks Project, Tag 04TR (blueprint: lem-pur-clopen-ringed-module-gluing). -/
def clopenTestInclusion {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.ProEt) :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
      (clopenTestPiece j U) ⟶ U :=
  MorphismProperty.Over.homMk (pullback.fst U.hom j) pullback.condition

/-- Additivity of restriction, used to form the component short complexes.
Source: Stacks Project, Tag 04TR (blueprint: lem-pur-clopen-ringed-module-gluing).
Proof: restriction evaluates each linear morphism on the same test object, so it
preserves sums of morphisms componentwise (step 3 of the node). -/
theorem clopenModuleRestriction_additive {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology X) RingCat.{u}) :
    (clopenModuleRestriction.{t, u, v} j R).Additive := by
  sorry

attribute [instance] clopenModuleRestriction_additive

/-- Restriction to all members of a finite clopen family.
Source: Stacks Project, Tag 04TS (blueprint: lem-pur-clopen-ringed-module-gluing). -/
abbrev clopenRestriction {X : Scheme.{t}} {I : Type w} {Y : I → Scheme.{t}}
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (R : Sheaf (topology X) RingCat.{u}) :=
  Functor.pi' (fun i ↦ clopenModuleRestriction.{t, u, v} (j i) R)

/-- The diagonal identification of a component object with its own base change.
This is the unit of the actual composition/base-change adjunction.
Source: Stacks Project, Tag 04TS (blueprint: lem-pur-clopen-ringed-module-gluing). -/
abbrev clopenDiagonal {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (W : Y.ProEt) :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial).unit.app W

/-- Exact gluing of arbitrary commutative-ring module sheaves on a finite clopen cover.
The section equivalences specify the product formula for G, its componentwise maps,
its scalar action, its restriction maps, the restriction unit and the projection counit.
The functors e_i are characterized as G applied to a tuple supported in coordinate i.
The bicone with vertex the identity is the natural direct-sum decomposition.

Source: Stacks Project, Tags 04TQ, 04TR, 04TS and 03DB
(blueprint: lem-pur-clopen-ringed-module-gluing).

Proof plan, following the node's steps:
1. Identify each component site with the slice by weaklyEtale_localization. Pull back
   the finite clopen cover to every test object; etalePrecoverage_le_proetalePrecoverage
   makes it a pro-etale cover. Distinct overlaps are empty and diagonal overlaps are
   the component itself.
2. The empty cover forces every module's sections on the empty object to be zero.
   Consequently the overlap isomorphisms are unique and satisfy the cocycle condition.
3. Form the product presheaf with componentwise addition, maps and restricted R-actions.
4. Apply exists_moduleSheaf_of_cover. The sheaf axiom identifies its sections with that
   product, proving the prescribed product presheaf is a sheaf, without choosing its data
   from a mere existence assertion.
5. Restriction of sections gives eta; projection on the diagonal gives epsilon. The
   sheaf axiom and the zero off-diagonal factors make them natural isomorphisms. Both
   triangle identities hold coordinatewise.
6. Insert a module in one coordinate and zero elsewhere, then apply G. Projection gives
   r_i e_i = id and r_i e_j = 0. The finite coordinate inclusions and projections give
   a bilimit bicone with vertex the identity.
7. Module categories are abelian. The tuple of kernels and cokernels has its universal
   property coordinatewise; transport across the equivalence gives preservation and
   detection, hence detection of exact short complexes. This uses preservation of limits
   and colimits by equivalences, not sectionwise surjectivity of sheaf epimorphisms.
8-9. Coefficient normalizations are stated separately in clopen_integral_coefficients;
   they follow by constant sheafification and sectionwise inverse limits.
10. Empty component sites have only empty objects, so all their module sheaves are zero.
    If the index is empty the covering hypothesis forces X empty; the product category
    is the category with one object and one arrow. -/
theorem clopen_ringed_module_gluing
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) RingCat.{u})
    (hcomm : ∀ (U : X.ProEtᵒᵖ) (a b : R.obj.obj U), a * b = b * a) :
    ∃ (G : (∀ i, ringedSiteModules.{max v w (t + 1)}
          ((clopenRingRestriction (j i)).obj R)) ⥤
          ringedSiteModules.{max v w (t + 1)} R)
      (η : 𝟭 _ ≅ clopenRestriction j R ⋙ G)
      (ε : G ⋙ clopenRestriction j R ≅ 𝟭 _),
      (∀ (F H : ringedSiteModules.{max v w (t + 1)} R) (f g : F ⟶ H) i,
        (clopenModuleRestriction (j i) R).map (f + g) =
          (clopenModuleRestriction (j i) R).map f +
            (clopenModuleRestriction (j i) R).map g) ∧
      Nonempty (Abelian (∀ i, ringedSiteModules.{max v w (t + 1)}
        ((clopenRingRestriction (j i)).obj R))) ∧
      (∀ (F H : ∀ i, ringedSiteModules.{max v w (t + 1)}
          ((clopenRingRestriction (j i)).obj R)) (f g : F ⟶ H),
        G.map (fun i ↦ f i + g i) = G.map f + G.map g) ∧
      PreservesFiniteLimits (clopenRestriction j R) ∧
      PreservesFiniteColimits (clopenRestriction j R) ∧
      PreservesFiniteLimits G ∧ PreservesFiniteColimits G ∧
      (∀ F, (clopenRestriction j R).map (η.hom.app F) ≫
        ε.hom.app ((clopenRestriction j R).obj F) = 𝟙 _) ∧
      (∀ F, η.hom.app (G.obj F) ≫ G.map (ε.hom.app F) = 𝟙 _) ∧
      (∃ σ : ∀ F U, (G.obj F).val.obj (op U) ≃+
          (∀ i, (F i).val.obj (op (clopenTestPiece (j i) U))),
        (∀ F U (a : R.obj.obj (op U)) x i,
          σ F U (a • x) i = R.obj.map (clopenTestInclusion (j i) U).op a • σ F U x i) ∧
        (∀ F (U V : X.ProEt) (f : V ⟶ U) x i,
          σ F V ((G.obj F).val.map f.op x) i =
            (F i).val.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (j i)).map f).op
              (σ F U x i)) ∧
        (∀ F H (f : F ⟶ H) U x i,
          σ H U ((G.map f).val.app (op U) x) i =
            (f i).val.app (op (clopenTestPiece (j i) U)) (σ F U x i)) ∧
        (∀ F U x i, σ ((clopenRestriction j R).obj F) U
            ((η.hom.app F).val.app (op U) x) i =
          F.val.map (clopenTestInclusion (j i) U).op x) ∧
        (∀ F i (W : (Y i).ProEt) x,
          ((ε.hom.app F) i).val.app (op W) x =
            (F i).val.map (clopenDiagonal (j i) W).op
              (σ F ((MorphismProperty.Over.map ⊤
                (inferInstance : WeaklyEtale (j i))).obj W) x i))) ∧
      (∃ e : ∀ i, ringedSiteModules.{max v w (t + 1)}
          ((clopenRingRestriction (j i)).obj R) ⥤
          ringedSiteModules.{max v w (t + 1)} R,
        (∀ i, Nonempty (e i ⋙ clopenModuleRestriction (j i) R ≅ 𝟭 _)) ∧
        (∀ i k, i ≠ k → ∀ M,
          IsZero ((e k ⋙ clopenModuleRestriction (j i) R).obj M)) ∧
        (∃ s : ∀ i, ringedSiteModules.{max v w (t + 1)}
            ((clopenRingRestriction (j i)).obj R) ⥤
            (∀ k, ringedSiteModules.{max v w (t + 1)}
              ((clopenRingRestriction (j k)).obj R)),
          ∀ i, e i = s i ⋙ G ∧
            Nonempty (s i ⋙ Pi.eval (fun k ↦ ringedSiteModules.{max v w (t + 1)}
              ((clopenRingRestriction (j k)).obj R)) i ≅ 𝟭 _) ∧
            (∀ k, k ≠ i → ∀ M, IsZero ((s i).obj M k))) ∧
        (∃ b : Bicone (fun i ↦ clopenModuleRestriction (j i) R ⋙ e i),
          b.pt = 𝟭 _ ∧ Nonempty b.IsBilimit)) ∧
      (∀ (F H : ringedSiteModules.{max v w (t + 1)} R) (f : F ⟶ H)
        (c : KernelFork f), Nonempty (IsLimit c) ↔
          ∀ i, Nonempty (IsLimit ((clopenModuleRestriction (j i) R).mapCone c))) ∧
      (∀ (F H : ringedSiteModules.{max v w (t + 1)} R) (f : F ⟶ H)
        (c : CokernelCofork f), Nonempty (IsColimit c) ↔
          ∀ i, Nonempty (IsColimit ((clopenModuleRestriction (j i) R).mapCocone c))) ∧
      (∀ S : ShortComplex (ringedSiteModules.{max v w (t + 1)} R),
        S.Exact ↔ ∀ i, (S.map (clopenModuleRestriction (j i) R)).Exact) ∧
      (∀ i, IsEmpty (Y i) → Nonempty
        (ringedSiteModules.{max v w (t + 1)} ((clopenRingRestriction (j i)).obj R) ≌
          Discrete PUnit)) ∧
      (IsEmpty I → IsEmpty X ∧ Nonempty
        (ringedSiteModules.{max v w (t + 1)} R ≌ Discrete PUnit)) := by
  sorry

/-- Constant finite-quotient sections, using the unit of commutative-ring sheafification.
Source: Stacks Project, Tag 04TR and blueprint order 1455
(blueprint: lem-pur-clopen-ringed-module-gluing). -/
abbrev clopenFiniteConstantSection (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{t}) (n : ℕ)
    (U : X.ProEt) :=
  (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
    ((toSheafify (topology X) ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
        (op U))

/-- Constant integral sections before passage to the completion.
Source: Stacks Project, Tag 04TR and blueprint order 1455
(blueprint: lem-pur-clopen-ringed-module-gluing). -/
abbrev clopenIntegralConstantSection (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{t}) (U : X.ProEt) :=
  (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
    ((toSheafify (topology X) ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app
        (op U))

/-- The coefficient identifications preserve constant sections, every finite projection,
all transition maps, and the actual constant-to-completed coefficient map.
The natural-number parameter n represents the positive exponent n+1 throughout.

Source: Stacks Project, localization Section 00XZ; Tags 04TR, 03CO and 03DB;
blueprint order 1455 (blueprint: lem-pur-clopen-ringed-module-gluing).

Proof (steps 8-9 of the node): weaklyEtale_localization identifies constant sheaves
by their sheafification units. Naturality in the quotient homomorphisms makes these
identifications commute with every transition. The sheaf inverse limit is sectionwise;
apply the finite comparisons to each coordinate of a compatible tuple. The resulting
ring isomorphism is natural on test objects and commutes with every limit projection.
The map from integral constants is the limit lift of the quotient cone, so preservation
of each constant residue implies preservation of the integral constant section itself.
This uses def-weil-pbc-constant-sheaf, def-weil-pbc-sheafification,
def-weil-completed-integral-coefficients and def-pur-sheaf-inverse-limit, and does not
identify the completed ring with the discrete constant integral ring. -/
theorem clopen_integral_coefficients
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : Γ(X, ⊤)))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ (finite : ∀ i n,
        (clopenRingRestriction (j i)).obj (WeilConjectures.integralCoefficientSheaf l E X n) ≅
          WeilConjectures.integralCoefficientSheaf l E (Y i) n)
      (completed : ∀ i, (clopenRingRestriction (j i)).obj
          (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E X) ≅
        WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E (Y i)),
      (∀ i n (W : (Y i).ProEt),
        clopenFiniteConstantSection l E X n
            ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (j i))).obj W) ≫
            (finite i n).hom.hom.app (op W) =
          clopenFiniteConstantSection l E (Y i) n W) ∧
      (∀ i (n m : ℕ) (h : n ≤ m),
        (clopenRingRestriction (j i)).map
            ((WeilConjectures.integralCoefficientSheafSystem l E X).map (homOfLE h).op) ≫
            (finite i n).hom =
          (finite i m).hom ≫
            (WeilConjectures.integralCoefficientSheafSystem l E (Y i)).map (homOfLE h).op) ∧
      (∀ i n, (clopenRingRestriction (j i)).map
            (limit.π (WeilConjectures.integralCoefficientSheafSystem l E X) (op n)) ≫
            (finite i n).hom =
          (completed i).hom ≫
            limit.π (WeilConjectures.integralCoefficientSheafSystem l E (Y i)) (op n)) ∧
      (∀ i (W : (Y i).ProEt),
        clopenIntegralConstantSection l E X
            ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (j i))).obj W) ≫
            (WeilConjectures.integralConstantToCompletionOfUniverses l E X).hom.app
              (op ((MorphismProperty.Over.map ⊤
                (inferInstance : WeaklyEtale (j i))).obj W)) ≫
            (completed i).hom.hom.app (op W) =
          clopenIntegralConstantSection l E (Y i) W ≫
            (WeilConjectures.integralConstantToCompletionOfUniverses l E (Y i)).hom.app
              (op W)) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
