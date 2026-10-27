module

public import Sheaf.AlgebraicGeometry.SpaceCoherentAdicSystem
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Sheaf.AlgebraicGeometry.SpaceThickeningCoherentSystems
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
public import Mathlib.CategoryTheory.Adjunction.Unique

import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedCoherentModules
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealCorrespondence
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization

/-! # The closed-immersion dictionary for coherent adic systems

Source: Stacks Project, spaces-cohomology.tex, Tag 08AM;
spaces-more-morphisms.tex, Tags 08BC (first paragraph) and 08BF
(blueprint: lem-sfb-space-closed-adic-dictionary).

Positive level n+1 is indexed by n. Quotient comparisons retain their projections.
The auxiliary categories only package the coherent predicates and the specified
adjacent tensor-restriction isomorphisms occurring in this dictionary.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S}

/-- Coherent modules killed by the specified ideal power, as a full subcategory.
Source: Stacks, Tags 08AM and 08BF
(blueprint: lem-sfb-space-closed-adic-dictionary). -/
abbrev ClosedAdicKilled (J : QuasiCoherentIdeal X) (n : ℕ) : ObjectProperty X.Modules :=
  fun M ↦ ClosedAdicCoherent X M ∧ AdicPowerKills J n M

/-- Termwise direct image, including all natural-transformation components.
Source: Stacks, Tag 08BC, first paragraph
(blueprint: lem-sfb-space-closed-adic-dictionary). -/
def closedAdicPushDiagram (i : Z ⟶ X) :
    (ℕᵒᵖ ⥤ Z.Modules) ⥤ (ℕᵒᵖ ⥤ X.Modules) :=
  (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj (moduleDirectImage i)

/-- A coherent adic system all of whose terms are killed by the closed ideal.
Source: Stacks, Tag 08BC, first paragraph
(blueprint: lem-sfb-space-closed-adic-dictionary). -/
abbrev ClosedAdicKilledSystems (J K : QuasiCoherentIdeal X) :
    ObjectProperty (ℕᵒᵖ ⥤ X.Modules) :=
  fun F ↦ IsCoherentAdicSystem J F ∧ ∀ n : ℕ, AdicPowerKills K 1 (F.obj (op n))

/-- The coherent and adic equivalences, with their specified functors and quotients.
The ideal K is the kernel of the structural quotient map, expressed by its universal
property. The image factorization defines L = J O_Z without an arbitrary ideal choice.
Source: Stacks, Tags 08AM and 08BC, first paragraph
(blueprint: lem-sfb-space-closed-adic-dictionary).

Proof:
1. Apply lem-sfb-space-closed-coherent-modules to obtain Noetherianity of Z.
   The quasi-coherent closed-immersion equivalence is exact and fully faithful.
   On an affine etale chart Spec R of X, the inverse image is Spec B, B = R/H.
   Etale restriction and the scheme Zariski/etale equivalence identify direct image
   with restriction of scalars of the same B-module N (the affine tilde/Gamma theorem).
2. A coherent killed module on X has a quasi-coherent inverse on Z. Its finite
   generators over R also generate over B. The affine finite-type criterion and
   the locally Noetherian coherence criterion give coherence on the covering
   base-changed charts of Z, hence on Z. This restricts the quasi-coherent equivalence.
3. Put P = J(Spec R). The pullback ideal is PB by closed-ideal correspondence.
   Expanding products proves P^n N = (PB)^n N. The affine ideal-product theorem
   identifies the kernel of i_*Q -> i_*(Q/L^n Q) with J^n(i_*Q). Coherent subquotients
   remain coherent. The local quotient identity glues, since it preserves projections.
4. A module map acts on both quotients by [m] -> [a(m)]; every transition sends
   [m] to [m]. Thus the comparisons are natural in Q and in all positive levels.
5. Push systems forward termwise. The quotient identity gives precisely their
   annihilation and adjacent quotient conditions. Conversely lift every term and
   transition through the coherent equivalence; full faithfulness lifts each arrow
   uniquely and reflects every adjacent square. This gives the adic equivalence.
6. Applied to the quotient diagrams, the natural comparison of step 4 is exactly
   compatibility with completion. No inverse-limit exchange is asserted or needed. -/
theorem closedAdicDictionary (i : Z ⟶ X)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    (K J : QuasiCoherentIdeal X)
    (hK : ∃ w : K.val.arrow ≫ moduleStructureMap i = 0,
      Nonempty (IsLimit (KernelFork.ofι K.val.arrow w))) :
    (∀ T : Z.EtaleSite, IsLocallyNoetherian (Z.etaleForget.obj T)) ∧
    CompactSpace (Point Z.obj.obj) ∧ IsAbsolutelyQuasiSeparated Z ∧
    (∃ E : (ClosedAdicCoherent Z).FullSubcategory ≌
        (ClosedAdicKilled K 1).FullSubcategory,
      Nonempty (E.functor ⋙ ObjectProperty.ι (ClosedAdicKilled K 1) ≅
        ObjectProperty.ι (ClosedAdicCoherent Z) ⋙ moduleDirectImage i)) ∧
    ∃ L : QuasiCoherentIdeal Z,
      (∃ q : (moduleTensorPullback i).obj (J.val : X.Modules) ⟶ (L.val : Z.Modules),
        Epi q ∧ q ≫ L.val.arrow = idealTensorMap i J) ∧
      (∃ β : ObjectProperty.ι (ClosedAdicCoherent Z) ⋙ moduleDirectImage i ⋙
          coherentAdicCompletionDiagram J ≅
          ObjectProperty.ι (ClosedAdicCoherent Z) ⋙ coherentAdicCompletionDiagram L ⋙
            closedAdicPushDiagram i,
        ∀ (Q : (ClosedAdicCoherent Z).FullSubcategory) (n : ℕ),
          (adicQuotientModel J).projection ((moduleDirectImage i).obj Q.obj) n ≫
              (β.app Q).hom.app (op n) =
            (moduleDirectImage i).map ((adicQuotientModel L).projection Q.obj n)) ∧
      (∃ E : (IsCoherentAdicSystem L).FullSubcategory ≌
          (ClosedAdicKilledSystems J K).FullSubcategory,
        Nonempty (E.functor ⋙ ObjectProperty.ι (ClosedAdicKilledSystems J K) ≅
          ObjectProperty.ι (IsCoherentAdicSystem L) ⋙ closedAdicPushDiagram i)) := by
  sorry

/-- The coherent and adic equivalences preserve and reflect proper support.
The same recorded predicate tests a module on its constant diagram and an adic
system on its actual first term. The structural properties on Z are supplied,
so the definition's proof parameters add no hypotheses.
Source: Stacks, Tag 08BC, first paragraph; Tag 0CZI
(blueprint: lem-sfb-space-closed-adic-dictionary).

Proof:
7. A closed immersion is separated and finite type. Composing with p supplies
   hZsep and hZft; affine etale charts are quotients R -> R/H of finite type
   A-algebras. For their coherent module N,
   Ann_R(N) = q^{-1}(Ann_(R/H)(N)). The corresponding quotient rings are canonically
   isomorphic. Closed-ideal correspondence glues these identifications, so the
   scheme-theoretic supports are the same space with the same map to Spec A.
   The proper-carrier/support theorem converts each displayed closed-carrier
   condition into properness of this same support map. This proves both directions
   for coherent modules. For systems apply the assertion to their coherent first
   term: the direct-image diagram's first term is exactly i_*F_1. This is the
   existing CoherentAdicHasProperSupport definition on each side; no common proper
   carrier for all levels is imposed. -/
theorem closedAdicDictionary_properSupport {A : Type u} [CommRing A]
    {X Z : AlgebraicSpace (Spec (.of A))}
    (p : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (.of A))))) (i : Z ⟶ X)
    (hi : IsRepresentableWith (fun _ _ q ↦ IsClosedImmersion q.left) i.hom.hom)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    (hsep : MapIsSeparated p) (hft : MapIsFiniteType p) :
    ∃ (hZsep : MapIsSeparated (i ≫ p)) (hZft : MapIsFiniteType (i ≫ p)),
      (∀ (Q : Z.Modules), ClosedAdicCoherent Z Q →
        (CoherentAdicHasProperSupport (i ≫ p) hZsep hZft ((Functor.const ℕᵒᵖ).obj Q) ↔
          CoherentAdicHasProperSupport p hsep hft
            ((Functor.const ℕᵒᵖ).obj ((moduleDirectImage i).obj Q)))) ∧
      (∀ (L : QuasiCoherentIdeal Z) (F : (IsCoherentAdicSystem L).FullSubcategory),
        CoherentAdicHasProperSupport (i ≫ p) hZsep hZft F.obj ↔
          CoherentAdicHasProperSupport p hsep hft ((closedAdicPushDiagram i).obj F.obj)) := by
  sorry

/-- Direct-image composition is the mate of the tensor-normalized composition iso.
Source: Stacks, Tags 03D7 and 08BF
(blueprint: lem-sfb-space-closed-adic-dictionary). -/
def closedAdicDirectComposition {W V U : AlgebraicSpace S}
    (a : W ⟶ V) (b : V ⟶ U) (c : W ⟶ U) (w : a ≫ b = c) :
    moduleDirectImage a ⋙ moduleDirectImage b ≅ moduleDirectImage c :=
  Adjunction.rightAdjointUniq
    (((moduleTensorAdjunction b).comp (moduleTensorAdjunction a)).ofNatIsoLeft
      (moduleTensorComposition a b ≪≫ eqToIso (congrArg moduleTensorPullback w)))
    (moduleTensorAdjunction c)

/-- The actual ambient transition induced by the adjacent restriction and its unit.
Source: Stacks, Tag 08BF (blueprint: lem-sfb-space-closed-adic-dictionary). -/
def closedAdicRestrictionTransition {Y : ℕ → AlgebraicSpace S}
    {j : ∀ n : ℕ, Y n ⟶ Y (n + 1)} (i : ∀ n : ℕ, Y n ⟶ X)
    (w : ∀ n : ℕ, j n ≫ i (n + 1) = i n) (F : ClosedAdicRestrictionSystem Y j) (n : ℕ) :
    (moduleDirectImage (i (n + 1))).obj (F.term (n + 1)) ⟶
      (moduleDirectImage (i n)).obj (F.term n) :=
  (moduleDirectImage (i (n + 1))).map
      ((moduleTensorAdjunction (j n)).unit.app (F.term (n + 1)) ≫
        (moduleDirectImage (j n)).map (F.restriction n).hom) ≫
    (closedAdicDirectComposition (j n) (i (n + 1)) (i n) (w n)).hom.app (F.term n)

/-- The scheme Spec(A/I^(n+1)) over Spec A.
Source: Stacks, Tag 08BF (blueprint: lem-sfb-space-closed-adic-dictionary). -/
def closedAdicBase {A : Type u} [CommRing A] (I : Ideal A)
    (n : ℕ) : Over (Spec (.of A)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))

/-- The canonical closed immersion Spec(A/I^(n+1)) -> Spec A as a map of spaces over S.
Source: Stacks, Tag 08BF (blueprint: lem-sfb-space-closed-adic-dictionary). -/
def closedAdicBaseMap {A : Type u} [CommRing A] (I : Ideal A)
    (n : ℕ) : schemeSpace (closedAdicBase I n) ⟶
      schemeSpace (Over.mk (𝟙 (Spec (.of A)))) :=
  ObjectProperty.homMk ⟨yoneda.map (Over.homMk
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) rfl)⟩

/-- The thickening dictionary on objects and arrows, including tensor completion.
The pullback squares specify the actual X_n; j is its unique adjacent inclusion.
The chart equality hJ says exactly J = I O_X. No completeness of A is required.
Source: Stacks, Tag 08BF, the system convention; Tag 08AM at each level
(blueprint: lem-sfb-space-closed-adic-dictionary).

Proof:
8. On every scheme test, factorization through Spec(A/I^n) is equivalent to
   vanishing of I^n. Expanding products gives (I O_T)^n = I^n O_T. The closed-ideal
   correspondence therefore identifies X_n with V(J^n). Apply the coherent
   equivalence of steps 1 and 2 at every level.
9. Given the specified restrictions, push terms forward and form their transitions
   by the unit F_(n+1) -> j_*j^*F_(n+1), the given isomorphism, and direct-image
   composition. On an affine chart this is N tensor_(R/P^(n+1)) R/P^n = N/P^n N:
   m tensor a goes to [am], and [m] goes to m tensor 1. Balancing proves that these
   are well defined inverses. Thus these are exactly the adic quotient transitions.
10. Conversely lift every coherent term killed by J^n through the levelwise
   equivalence. Full faithfulness uniquely lifts the quotient-transition isomorphism
   to j^*F_(n+1) = F_n. It likewise lifts every arrow, and reflects its adjacent
   commutative squares. This gives the system equivalence with the displayed
   transition normalization. For a coherent M, the same local tensor maps identify
   i_*i^*M with M/J^nM and send its adjunction unit to m -> [m]. Uniqueness makes
   these comparisons natural in M and compatible with every quotient transition.
   They give R, alpha and sigma with the displayed unit/projection equation. -/
theorem closedAdicDictionary_thickenings {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (.of A))}
    (p : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (.of A)))))
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    (hsep : MapIsSeparated p) (hft : MapIsFiniteType p)
    (I : Ideal A) (J : QuasiCoherentIdeal X)
    (hJ : ∀ T : X.EtaleSite, IsAffine (X.etaleForget.obj T) →
      idealSectionImage J.val.arrow T =
      I.map (((Scheme.ΓSpecIso (.of A)).inv ≫
        (yoneda.preimage (T.obj.hom ≫ p.hom.hom)).left.appTop).hom))
    (Y : ℕ → AlgebraicSpace (Spec (.of A))) (i : ∀ n : ℕ, Y n ⟶ X)
    (b : ∀ n : ℕ, Y n ⟶ schemeSpace (closedAdicBase I n))
    (hb : ∀ n : ℕ, IsPullback (i n).hom (b n).hom p.hom (closedAdicBaseMap I n).hom)
    (j : ∀ n : ℕ, Y n ⟶ Y (n + 1)) (w : ∀ n : ℕ, j n ≫ i (n + 1) = i n) :
    (∀ n : ℕ, ∃ E : (ClosedAdicCoherent (Y n)).FullSubcategory ≌
        (ClosedAdicKilled J (n + 1)).FullSubcategory,
      Nonempty (E.functor ⋙ ObjectProperty.ι (ClosedAdicKilled J (n + 1)) ≅
        ObjectProperty.ι (ClosedAdicCoherent (Y n)) ⋙ moduleDirectImage (i n))) ∧
    ∃ E : ClosedAdicRestrictionSystem Y j ≌ (IsCoherentAdicSystem J).FullSubcategory,
      ∃ ρ : ∀ n : ℕ,
          ClosedAdicRestrictionSystem.evaluation n ⋙ moduleDirectImage (i n) ≅
            E.functor ⋙ ObjectProperty.ι (IsCoherentAdicSystem J) ⋙
              (CategoryTheory.evaluation ℕᵒᵖ X.Modules).obj (op n),
        (∀ (F : ClosedAdicRestrictionSystem Y j) (n : ℕ),
          (ρ (n + 1)).hom.app F ≫
              (E.functor.obj F).obj.map (homOfLE (Nat.le_succ n)).op =
            closedAdicRestrictionTransition i w F n ≫ (ρ n).hom.app F) ∧
        ∃ (R : (ClosedAdicCoherent X).FullSubcategory ⥤ ClosedAdicRestrictionSystem Y j)
          (σ : R ⋙ E.functor ⋙ ObjectProperty.ι (IsCoherentAdicSystem J) ≅
            ObjectProperty.ι (ClosedAdicCoherent X) ⋙ coherentAdicCompletionDiagram J)
          (α : ∀ n : ℕ, R ⋙ ClosedAdicRestrictionSystem.evaluation n ≅
            ObjectProperty.ι (ClosedAdicCoherent X) ⋙ moduleTensorPullback (i n)),
          ∀ (M : (ClosedAdicCoherent X).FullSubcategory) (n : ℕ),
            (moduleTensorAdjunction (i n)).unit.app M.obj ≫
                (moduleDirectImage (i n)).map ((α n).inv.app M) ≫
                (ρ n).hom.app (R.obj M) ≫ (σ.app M).hom.app (op n) =
              (adicQuotientModel J).projection M.obj n := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
