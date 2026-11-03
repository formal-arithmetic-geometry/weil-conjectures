/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedOpenCounitSiteTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
import WeilConjectures.Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.SixFunctors.Etale.Derived.Supports
import Mathlib.Algebra.FiveLemma
import Mathlib.CategoryTheory.Triangulated.Yoneda
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenCoverShriekTriangle
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp

/-! # Finite-open-cover locality for a prescribed finite-ring counit

Source: blueprint, sec-smooth-purity/sk-def-sp-representing-pair,
det-sp-representing-pair-gluing.proof.md, open-cover triangle and Hom five lemma
(blueprint: lem-sp-finite-ring-counit-local-representability).

Local Hom maps are written after transport along the canonical comparison
`F_X j_{W!} ≅ F_W`. The inverse open-adjunction Hom equivalence is precisely
`a ↦ j_{W!}(a) ≫ ε_{W,H}`. Thus these are the restricted maps of the given counit,
without choosing a new counit or assuming any local representability of a tower.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits ZeroObject
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.ProEtale

private def counitHomNat {C D : Type*} [Category.{w} C] [Category.{w} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (H : C) (K : D) (e : F.obj H ⟶ K) :
    preadditiveYoneda.obj H ⟶ F.op ⋙ preadditiveYoneda.obj K where
  app M := AddCommGrpCat.ofHom
    { toFun := fun a ↦ F.map a ≫ e
      map_zero' := by simp
      map_add' := by
        intro x y
        change F.map (x + y) ≫ e = F.map x ≫ e + F.map y ≫ e
        rw [F.map_add, Preadditive.add_comp] }
  naturality _ _ h := by
    ext a
    change F.map (h.unop ≫ a) ≫ e = F.map h.unop ≫ (F.map a ≫ e)
    rw [F.map_comp, Category.assoc]

private def homIsoLocus
    {C : Type*} [Category C] [HasShift C ℤ]
    {G G' : Cᵒᵖ ⥤ AddCommGrpCat} (η : G ⟶ G') : ObjectProperty C :=
  fun M ↦ ∀ n : ℤ, IsIso (η.app (Opposite.op (M⟦n⟧)))

private theorem etale_ctf_bounded_iff
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T N ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T N := by
  constructor
  · rintro ⟨hc, a, b, _, h⟩
    exact ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff N a).mpr
      (fun i hi ↦ h i (Or.inl hi))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff N b).mpr
        (fun i hi ↦ h i (Or.inr hi))⟩⟩,
      fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i)⟩
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (hc i), min a b, b, min_le_right _ _, ?_⟩
    intro i hi
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff N a).mp ha i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff N b).mp hb i hi

private theorem intrinsic_ctf_iff_origin
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    exceptionalTransportProEtaleObjects A T M ↔
      (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T).map
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory M := by
  let N := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  have hc := exceptionalTransport_constructible_comparison A T
  constructor
  · rintro ⟨hbd, hcs, a, b, hab, ht⟩
    have hbc : (Etale.DerivedCategory.isBoundedConstructible A T).map N M :=
      (congrFun hc M).mp ⟨hbd, hcs⟩
    obtain ⟨L, hL, ⟨e⟩⟩ := hbc
    have ht' : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) T a b (N.obj L) :=
      (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm ht
    exact ⟨L, ⟨(etale_ctf_bounded_iff A T L).mp hL, a, b,
      (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b L).mp ht'⟩, ⟨e⟩⟩
  · rintro ⟨L, ⟨hL, a, b, ht⟩, ⟨e⟩⟩
    have hbc : (Etale.DerivedCategory.isBoundedConstructible A T).map N M :=
      ⟨L, (etale_ctf_bounded_iff A T L).mpr hL, ⟨e⟩⟩
    obtain ⟨hbd, hcs⟩ := (congrFun hc M).mpr hbc
    refine ⟨hbd, hcs, min a b, b, min_le_right _ _, ?_⟩
    exact (_root_.DerivedCategory.torAmplitudeIn _ (min a b) b).prop_of_iso e
      ((DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff (min a b) b L).mpr
        (Etale.DerivedCategory.torAmplitudeIn.mono (min_le_left _ _) le_rfl ht))

private noncomputable def etaleOpenComp
    (A : Type (u + 1)) [CommRing A] {V U X : Scheme.{u}}
    (j' : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion j'] [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) (j' ≫ j)).mapDerivedCategory ≅
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j').mapDerivedCategory ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (Etale.openImmersionLowerShriekComp _ j' j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

private abbrev etaleD (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))

private noncomputable abbrev etaleJ (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (j : Z ⟶ X) [IsOpenImmersion j] :=
  (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory

private def openTestLocus (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (P : ObjectProperty (etaleD A X)) (W : X.Opens) : Prop :=
  ∀ (Z : Scheme.{u}) (j : Z ⟶ X) [IsOpenImmersion j] (N : etaleD A Z),
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Z N →
      j.opensRange = W → P ((etaleJ A j).obj N)

private lemma openTestLocus_sup
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (P : ObjectProperty (etaleD A X)) [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
    (U V : X.Opens) (hU : openTestLocus A X P U) (hV : openTestLocus A X P V)
    (hUV : openTestLocus A X P (U ⊓ V)) : openTestLocus A X P (U ⊔ V) := by
  intro Z j _ N hN hj
  let U' := j ⁻¹ᵁ U
  let V' := j ⁻¹ᵁ V
  have hcover : U' ⊔ V' = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, ← hj, ← j.image_top_eq_opensRange,
      j.preimage_image_eq]
  let N' : _root_.DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨N, hN.1.1.1⟩
  obtain ⟨α, β, δ, hT⟩ := Etale.exists_distinguished_openCover_lowerShriek A U' V' hcover N'
  let L := _root_.DerivedCategory.Plus.ι ⋙ etaleJ A j
  let B (W : Z.Opens) :=
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) W.ι).mapDerivedCategoryPlus.obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) W.ι).mapDerivedCategoryPlus.obj N')
  let p (W : Z.Opens) : L.obj (B W) ≅ (etaleJ A (W.ι ≫ j)).obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) W.ι).mapDerivedCategory.obj N) :=
    (etaleJ A j).mapIso
      ((Functor.mapDerivedCategoryPlusCompatibility
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) W.ι)).app _ ≪≫
        (etaleJ A W.ι).mapIso
          ((Functor.mapDerivedCategoryPlusCompatibility
            (Etale.upperStar (ModuleCat.{u + 1} A) W.ι)).app N')) ≪≫
      (etaleOpenComp A W.ι j).symm.app _
  have hW (W : Z.Opens) (S : X.Opens) (hS : openTestLocus A X P S)
      (he : (W.ι ≫ j).opensRange = S) : P (L.obj (B W)) :=
    P.prop_of_iso (p W).symm (hS _ _ _
      (Etale.constructibleFiniteTor_mapDerivedCategory_upperStar A W.ι hN) he)
  have hPU : P (L.obj (B U')) := hW _ U hU (by
    dsimp [U']
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, hj]
    exact inf_eq_right.mpr le_sup_left)
  have hPV : P (L.obj (B V')) := hW _ V hV (by
    dsimp [V']
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, hj]
    exact inf_eq_right.mpr le_sup_right)
  have hPUV : P (L.obj (B (U' ⊓ V'))) := hW _ (U ⊓ V) hUV (by
    change (((j ⁻¹ᵁ U) ⊓ (j ⁻¹ᵁ V)).ι ≫ j).opensRange = U ⊓ V
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      ← Scheme.Hom.preimage_inf, Scheme.Hom.image_preimage_eq_opensRange_inf, hj]
    exact inf_eq_right.mpr (inf_le_left.trans le_sup_left))
  have : PreservesBinaryBiproducts L := preservesBinaryBiproducts_of_preservesBiproducts L
  have hPB : P (L.obj (B U' ⊞ B V')) := by
    apply P.prop_of_iso (L.mapBiprod _ _).symm
    exact P.ext_of_isTriangulatedClosed₂ _
      (binaryBiproductTriangle_distinguished _ _) hPU hPV
  exact P.ext_of_isTriangulatedClosed₃ _ (L.map_distinguished _ hT) hPUV hPB

private lemma finite_union_induction
    {B : Type*} [DistribLattice B] [OrderBot B] [OrderTop B]
    (P : B → Prop) (hbot : P ⊥)
    (hsup : ∀ U V, P U → P V → P (U ⊓ V) → P (U ⊔ V))
    {I : Type*} (U : I → B) (s : Finset I)
    (hlocal : ∀ t : Finset I, t ⊆ s → t.Nonempty → P (t.inf U)) : P (s.sup U) := by
  classical
  induction s using Finset.induction_on generalizing U with
  | empty => simpa using hbot
  | @insert i s hi ih =>
    rw [Finset.sup_insert]
    have h₁ : P (U i) := by
      simpa using hlocal {i} (by simp) (Finset.singleton_nonempty i)
    have h₂ : P (s.sup U) := ih U (fun t ht hn ↦ hlocal t (ht.trans (by simp)) hn)
    apply hsup _ _ h₁ h₂
    rw [Finset.sup_inf_distrib_left]
    apply ih
    intro t ht hn
    have he : t.inf (fun j ↦ U i ⊓ U j) = (insert i t).inf U := by
      obtain ⟨j, hj⟩ := hn
      apply le_antisymm
      · apply Finset.le_inf
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact (Finset.inf_le hj).trans inf_le_left
        · exact (Finset.inf_le hk).trans inf_le_right
      · apply Finset.le_inf
        intro k hk
        exact le_inf (Finset.inf_le (Finset.mem_insert_self _ _))
          (Finset.inf_le (Finset.mem_insert_of_mem hk))
    rw [he]
    exact hlocal _ (Finset.insert_subset_insert i ht) (Finset.insert_nonempty _ _)

private lemma openTestLocus_of_inclusion
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (P : ObjectProperty (etaleD A X)) [P.IsClosedUnderIsomorphisms]
    (W : X.Opens)
    (hW : ∀ (N : etaleD A W.toScheme),
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) W.toScheme N →
        P ((etaleJ A W.ι).obj N)) : openTestLocus A X P W := by
  intro Z j _ N hN hj
  subst W
  let e := j.isoOpensRange
  let N' := (Etale.upperStar (ModuleCat.{u + 1} A) e.inv).mapDerivedCategory.obj N
  have hN' : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} A) j.opensRange.toScheme N' :=
    Etale.constructibleFiniteTor_mapDerivedCategory_upperStar A e.inv hN
  let i : (etaleJ A e.hom).obj N ≅ N' :=
    (Functor.mapDerivedCategoryNatIso
      (Etale.upperStarIsoOpenImmersionLowerShriekInv (ModuleCat.{u + 1} A) e.symm)).symm.app N
  let p : (etaleJ A j).obj N ≅ (etaleJ A j.opensRange.ι).obj N' :=
    (eqToIso (by simp only [e, Scheme.Hom.isoOpensRange_hom_ι])) ≪≫
      (etaleOpenComp A e.hom j.opensRange.ι).app N ≪≫
      (etaleJ A j.opensRange.ι).mapIso i
  exact P.prop_of_iso p.symm (hW N' hN')

private lemma openTestLocus_bot
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (P : ObjectProperty (etaleD A X)) [P.IsClosedUnderIsomorphisms] [P.ContainsZero] :
    openTestLocus A X P ⊥ := by
  intro Z j _ N _ hj
  have : IsEmpty Z := ⟨fun z ↦ by
    have hz : j z ∈ j.opensRange := ⟨z, rfl⟩
    simp only [hj, TopologicalSpace.Opens.mem_bot] at hz⟩
  exact P.prop_of_isZero
    ((etaleJ A j).map_isZero (Etale.isZero_derivedCategory_of_isEmpty _ Z N))

-- The stronger proof does not use the retained preservation and ctf hypotheses.
set_option linter.unusedVariables false in
/-- A prescribed counit represents compact-support Hom if its restrictions do so on
all nonempty indexed intersections of a finite open cover, including empty schemes.
The coefficient category is the ordinary fixed-module presentation of constant-ring
module sheaves. `exceptionalTransportProEtaleObjects` is the recorded intrinsic
bounded-constructible finite-Tor predicate; it imposes no etale-origin condition.

Source: blueprint, sec-smooth-purity/sk-def-sp-representing-pair,
det-sp-representing-pair-gluing.proof.md, paragraphs 1--2
(blueprint: lem-sp-finite-ring-counit-local-representability).

Proof:
1. Finite type over a field makes X Noetherian. The intrinsic constructibility
comparison and detection of Tor amplitude identify every intrinsic ctf object
with the comparison image of an etale bounded constructible finite-Tor object.
The converse holds as well, widening the Tor interval if its endpoints are reversed.
2. The maps a ↦ F(a) ≫ e form a natural transformation of additive contravariant
Hom functors. Its locus of bijectivity in every shift is a triangulated object
property: exact Hom sequences for a triangle and its rotations form a commutative
five-term ladder, and the abelian-group five lemma supplies the middle bijection.
The property contains zero and is invariant under isomorphisms and shifts.
3. Pull this property back along etale-to-proetale comparison. For an open W and
an etale ctf object N, apply the local hypothesis to every shift of its comparison
image. The actual open Hom adjunction identifies that local function with the
Hom transformation at j_! of the image. The canonical extension comparison and
shift isomorphisms therefore give the pulled-back property at etale j_! N.
4. To handle all open immersions with image W, factor the immersion through its
canonical isomorphism with W. Extension along that isomorphism is pullback along
its inverse; it preserves ctf objects. Composition of extension by zero then
reduces the claim to step 3.
5. For an immersion with image U ∪ V, pull U and V back to its source. Restrict an
etale ctf test to those two opens and their intersection. The existing etale
Mayer–Vietoris triangle, mapped by extension to X, has these three extensions as
its first two terms and the original extension as its third. The triangulated
property, including closure under biproducts, proves the binary-union step.
6. On the empty scheme all sheaves and derived objects are zero, giving the
empty-union base case. Induct on a finite set of opens. For the intersection
of the last open with the preceding union apply the same induction to the
family of intersections; each test is an original nonempty indexed intersection.
7. Apply the result to the full cover and the identity immersion. Transport
along the identity-extension isomorphism and the etale-origin isomorphism to
obtain the desired bijection. Functoriality and associativity give naturality.
The proof keeps e fixed throughout and needs no preservation assertion for F
beyond its existing additive triangulated structure.
-/
theorem finiteRingCounit_localRepresentability
    (k : Type u) [Field k] (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aY = aX) (c : Compactification f)
    (hpres : ∀ (W : X.Opens)
      (P : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology W.toScheme)
        (ModuleCat.{u + 1} A))),
      exceptionalTransportProEtaleObjects A W.toScheme P →
      exceptionalTransportProEtaleObjects A Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (c.precomp W.ι)).obj P))
    (H : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (hH : exceptionalTransportProEtaleObjects A X H)
    (hK : exceptionalTransportProEtaleObjects A Y K)
    (e : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj H ⟶ K)
    (I : Type v) [Finite I] (U : I → X.Opens) (hcover : iSup U = ⊤)
    (hlocal : ∀ (J : Finset I), J.Nonempty → ∀ (W : X.Opens),
      W = ⨅ i : J, U i.val →
      ∀ (P : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology W.toScheme)
        (ModuleCat.{u + 1} A))),
      exceptionalTransportProEtaleObjects A W.toScheme P →
      Function.Bijective
        (fun a : P ⟶ (openImmersionRestriction (ModuleCat.{u + 1} A)
            W.ι).mapDerivedCategory.obj H ↦
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
            (((unboundedOpenProEtaleAdjunction A W.ι).homEquiv P H).symm a) ≫ e)) :
    (∀ (M : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))),
      exceptionalTransportProEtaleObjects A X M →
      Function.Bijective (fun a : M ⟶ H ↦
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map a ≫ e)) ∧
    (∀ (M M' : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))),
      exceptionalTransportProEtaleObjects A X M →
      exceptionalTransportProEtaleObjects A X M' → ∀ (h : M' ⟶ M) (a : M ⟶ H),
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map (h ≫ a) ≫ e =
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map h ≫
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map a ≫ e)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  let : IsNoetherian X := {}
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let ν := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let η := counitHomNat F H K e
  let Q := homIsoLocus η
  let P := Q.inverseImage ν
  have hlocal' (J : Finset I) (hJ : J.Nonempty) : openTestLocus A X P (J.inf U) := by
    apply openTestLocus_of_inclusion A X P
    intro N hN
    let W := J.inf U
    let : IsNoetherian W.toScheme := {}
    change Q (ν.obj ((etaleJ A W.ι).obj N))
    intro n
    let Nn := N⟦n⟧
    have hNn : Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} A) W.toScheme Nn :=
      Etale.DerivedCategory.boundedConstructibleFiniteTor.shift hN n
    let νW := (comparisonUpperStar (ModuleCat.{u + 1} A) W.toScheme).mapDerivedCategory
    have hPn : exceptionalTransportProEtaleObjects A W.toScheme (νW.obj Nn) :=
      (intrinsic_ctf_iff_origin A W.toScheme _).mpr ⟨Nn, hNn, ⟨Iso.refl _⟩⟩
    let B := (openImmersionLowerShriek (ModuleCat.{u + 1} A) W.ι).mapDerivedCategory.obj
      (νW.obj Nn)
    have hB : Function.Bijective (η.app (Opposite.op B)).hom := by
      change Function.Bijective (fun a : B ⟶ H ↦ F.map a ≫ e)
      apply (Function.Bijective.of_comp_iff _
        ((unboundedOpenProEtaleAdjunction A W.ι).homEquiv (νW.obj Nn) H).symm.bijective).mp
      exact hlocal J hJ W (by simp only [W, Finset.inf_eq_iInf, iInf_subtype]) _ hPn
    have : IsIso (η.app (Opposite.op B)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hB
    let p : (ν.obj ((etaleJ A W.ι).obj N))⟦n⟧ ≅ B :=
      ((etaleJ A W.ι ⋙ ν).commShiftIso n).symm.app N ≪≫
        (unboundedOpenExtensionComparison A W.ι).app Nn
    exact η.isIso_app_of_iso p.symm.op
  have htop : openTestLocus A X P ⊤ := by
    have hh := finite_union_induction (openTestLocus A X P)
      (openTestLocus_bot A X P) (openTestLocus_sup A X P) U Finset.univ
      (fun J _ hJ ↦ hlocal' J hJ)
    simpa only [Finset.sup_eq_iSup, Finset.mem_univ, iSup_pos, hcover] using hh
  constructor
  · intro M hM
    obtain ⟨N, hN, ⟨p⟩⟩ := (intrinsic_ctf_iff_origin A X M).mp hM
    have hPN : P ((etaleJ A (𝟙 X)).obj N) :=
      htop X (𝟙 X) N hN (Scheme.Hom.opensRange_of_isIso _)
    let eId : (etaleJ A (𝟙 X)).obj N ≅ N :=
      (Functor.mapDerivedCategoryNatIso
        ((Etale.upperStarIsoOpenImmersionLowerShriekInv (ModuleCat.{u + 1} A)
          (Iso.refl X)).symm ≪≫ Etale.upperStarId (ModuleCat.{u + 1} A) X) ≪≫
        Functor.mapDerivedCategoryIdIso _).app N
    have hQN : Q (ν.obj N) := P.prop_of_iso eId hPN
    have hQM : Q M := Q.prop_of_iso p hQN
    have := hQM 0
    have : IsIso (η.app (Opposite.op M)) :=
      η.isIso_app_of_iso ((shiftFunctorZero _ ℤ).app M).op
    change Function.Bijective (η.app (Opposite.op M)).hom
    exact (ConcreteCategory.isIso_iff_bijective (η.app (Opposite.op M))).mp inferInstance
  · intro M M' hM hM' h a
    simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry.ProEtale
