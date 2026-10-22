module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness
import Sheaf.SixFunctors.BrownHypothesesSmall
import Sheaf.SixFunctorsBasics.BrownHypothesesStructural
import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# Hypotheses of Brown representability

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-brown-hypotheses/_section.md
(blueprint: sk-lem-brown-hypotheses).

`BrownHypothesesFor` bundles the conclusion, using the canonical full-subcategory shift.
`brownHypotheses` asserts it for the standing scheme and the six admissible coefficients.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory

/-- The conclusions of the Brown-hypotheses lemma, for a specified coefficient ring.
The localizing closure and constructible finite-Tor property are the recorded definitions.
All size assertions and coproducts use the fixed indexing universe `u + 1`. The existential
triangulation witness installs the canonical shift inherited from the ambient derived
category; no independently chosen shift is allowed. The coproduct witness also precedes
compactness and generation, so these clauses cannot be vacuous for lack of coproducts.
This is only a bundle of the lemma's conclusions, not an assertion for arbitrary rings.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-brown-hypotheses/_section.md, conclusion
(blueprint: sk-lem-brown-hypotheses). -/
def BrownHypothesesFor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) : Prop :=
  let S := constantModelBoundedConstructible Λ X ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K
  let L := localizingClosureProEtale Λ X
  LocallySmall.{u + 1} L.FullSubcategory ∧
    ∃ hTri : L.IsTriangulated,
      letI := hTri
      L.IsClosedUnderIsomorphisms ∧
        S.IsTriangulated ∧ S.IsClosedUnderIsomorphisms ∧ S.IsStableUnderRetracts ∧
        ObjectProperty.EssentiallySmall.{u + 1} S ∧
        IsIdempotentComplete L.FullSubcategory ∧
        ∃ hSums : HasCoproducts.{u + 1} L.FullSubcategory,
          letI := hSums
          ∀ (G : Type (u + 1)) [Category.{u + 1} G] (e : G ≌ S.FullSubcategory)
            (hL : ∀ g : G, L (e.functor.obj g).1),
            (∀ g : G, IsCompactObject
              (⟨(e.functor.obj g).1, hL g⟩ : L.FullSubcategory)) ∧
            IsTriangulatedGeneratingFamily
              (fun g : G ↦ (⟨(e.functor.obj g).1, hL g⟩ : L.FullSubcategory))

private theorem localizingClosure_isLocalizing
    {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : ObjectProperty C) : IsLocalizingSubcategory (localizingClosure S) := by
  have hIso : (localizingClosure S).IsClosedUnderIsomorphisms := by
    constructor
    intro X Y e hX P hP hSP
    let := hP.2.1
    exact P.prop_of_iso e (hX P hP hSP)
  let := hIso
  have hShift : (localizingClosure S).IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    intro X hX P hP hSP
    let := hP.1
    exact P.le_shift n X (hX P hP hSP)
  let := hShift
  have hZero : (localizingClosure S).ContainsZero := by
    refine ⟨HasZeroObject.zero.choose, HasZeroObject.zero.choose_spec, ?_⟩
    intro P hP hSP
    let := hP.1
    let := hP.2.1
    exact P.prop_zero
  let := hZero
  have hExt : (localizingClosure S).IsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.mk' fun T hT h₁ h₃ P hP hSP ↦ by
      let := hP.1
      let := hP.2.1
      exact P.ext_of_isTriangulatedClosed₂ T hT (h₁ P hP hSP) (h₃ P hP hSP)
  let := hExt
  refine ⟨⟨⟩, hIso, ?_⟩
  intro I F hF hLF
  let := hF
  change localizingClosure S (colimit F)
  intro P hP hSP
  exact hP.2.2 F hF (fun i ↦ hLF i P hP hSP)

private theorem isZero_of_localizingClosure_orthogonal
    {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : ObjectProperty C) [S.IsStableUnderShift ℤ]
    (K : C) (hK : localizingClosure S K) (horth : S.rightOrthogonal K) : IsZero K := by
  let R := S.rightOrthogonal.leftOrthogonal
  have hR : IsLocalizingSubcategory R := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I F hF hRF
    let := hF
    change R (colimit F)
    intro Z f hZ
    apply colimit.hom_ext
    intro j
    simpa using hRF j.as (colimit.ι F j ≫ f) hZ
  have hRK := hK R hR (fun X hX Z f hZ ↦ hZ f hX)
  exact (IsZero.iff_id_eq_zero K).mpr (hRK (𝟙 K) horth)

private theorem localizingClosure_generatingFamily
    {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (S : ObjectProperty C) [S.IsStableUnderShift ℤ]
    [hL : (localizingClosure S).IsTriangulated]
    {I : Type*} (E : I → (localizingClosure S).FullSubcategory) [HasCoproduct E]
    (hE : ∀ X : C, S X → ∃ i : I, Nonempty (X ≅ (E i).obj)) :
    IsTriangulatedGeneratingFamily E := by
  classical
  intro K hK
  by_contra! hn
  have hzero (f : ∐ E ⟶ K) : f = 0 := by
    have h := hn 0 (f ≫ (shiftFunctorZero _ ℤ).inv.app K)
    apply (cancel_mono ((shiftFunctorZero _ ℤ).inv.app K)).mp
    simpa using h
  have horth : S.rightOrthogonal K.obj := by
    intro X f hX
    obtain ⟨i, ⟨e⟩⟩ := hE X hX
    let a : E i ⟶ K := ObjectProperty.homMk (e.inv ≫ f)
    have ha : a = 0 := by
      have h := congrArg (fun g ↦ Sigma.ι E i ≫ g)
        (hzero (Sigma.desc (Pi.single i a)))
      simpa using h
    have h := congrArg (fun g ↦ e.hom ≫ g.hom) ha
    simpa [a] using h
  exact hK (IsZero.of_full_of_faithful_of_isZero (localizingClosure S).ι K
    (isZero_of_localizingClosure_orthogonal S K.obj K.property horth))

/-- The formal assembly of Brown's hypotheses from thickness, smallness and compactness.
Generation follows from the intersection defining the localizing closure, so it requires
no extra cohomological finiteness assumption beyond the compactness input.

Source: blueprint main-20261015, sk-lem-brown-hypotheses.proof.md, paragraphs 1--2.
(blueprint: sk-lem-brown-hypotheses). -/
private theorem brownHypothesesFor_of_compact
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [LocallySmall.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory]
    [HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory]
    [IsIdempotentComplete (localizingClosureProEtale Λ X).FullSubcategory]
    (hS :
      (constantModelBoundedConstructible Λ X ⊓
        fun K ↦ DerivedCategory.finiteTorAmplitude _ K).IsTriangulated ∧
      (constantModelBoundedConstructible Λ X ⊓
        fun K ↦ DerivedCategory.finiteTorAmplitude _ K).IsClosedUnderIsomorphisms ∧
      (constantModelBoundedConstructible Λ X ⊓
        fun K ↦ DerivedCategory.finiteTorAmplitude _ K).IsStableUnderRetracts ∧
      ObjectProperty.EssentiallySmall.{u + 1}
        (constantModelBoundedConstructible Λ X ⊓
          fun K ↦ DerivedCategory.finiteTorAmplitude _ K))
    (hcompact : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      (constantModelBoundedConstructible Λ X K.obj ∧
        DerivedCategory.finiteTorAmplitude _ K.obj) → IsCompactObject K) :
    BrownHypothesesFor Λ X := by
  let S := constantModelBoundedConstructible Λ X ⊓
    fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  let L := localizingClosureProEtale Λ X
  have hLoc : IsLocalizingSubcategory L := localizingClosure_isLocalizing S
  let _ : (localizingClosure S).IsTriangulated := hLoc.1
  let _ : S.IsTriangulated := hS.1
  let _ : HasCoproducts.{u + 1} L.FullSubcategory := inferInstance
  refine ⟨inferInstance, hLoc.1, hLoc.2.1, hS.1, hS.2.1, hS.2.2.1,
    hS.2.2.2, inferInstance, inferInstance, ?_⟩
  intro G _ e hL
  refine ⟨fun g ↦ hcompact _ (e.functor.obj g).property, ?_⟩
  have hc : HasCoproduct (fun g : G ↦
      (⟨(e.functor.obj g).obj, hL g⟩ : L.FullSubcategory)) := inferInstance
  let := hc
  apply localizingClosure_generatingFamily (E := fun g : G ↦
    (⟨(e.functor.obj g).obj, hL g⟩ : L.FullSubcategory)) S
  intro Y hY
  let B : S.FullSubcategory := ⟨Y, hY⟩
  exact ⟨e.inverse.obj B, ⟨(S.ι.mapIso (e.counitIso.app B)).symm⟩⟩

/-- Compactness transports by precomposition with an isomorphism. -/
private theorem compact_of_iso
    {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{u} C]
    {K L : C} (e : K ≅ L) (hL : IsCompactObject L) : IsCompactObject K := by
  classical
  intro I A
  let d := DirectSum.map (fun i ↦ Preadditive.leftComp (A i) e.hom)
  have hd : Function.Bijective d :=
    ⟨(DirectSum.map_injective _).2 (fun i ↦ e.symm.homFromEquiv.injective),
      (DirectSum.map_surjective _).2 (fun i ↦ e.symm.homFromEquiv.surjective)⟩
  let post := Preadditive.leftComp (∐ A) e.hom
  have hp : Function.Bijective post := e.symm.homFromEquiv.bijective
  let a := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp K (Sigma.ι A i))
  let b := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp L (Sigma.ι A i))
  have square : a.comp d = post.comp b := by
    apply DirectSum.addHom_ext
    intro i f
    simp only [AddMonoidHom.comp_apply]
    dsimp [a, b, d]
    rw [DirectSum.map_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    exact Category.assoc _ _ _
  have hb : Function.Bijective b := hL I A
  have hcomp : Function.Bijective (a ∘ d) := by
    change Function.Bijective (a.comp d)
    rw [square]
    exact hp.comp hb
  exact (Function.Bijective.of_comp_iff a hd).mp hcomp

/-- The full Brown bundle in the geometric finite-field setting for a finite
extension of the p-adic rationals. This uses the actual compactness dependency,
whose hypotheses do not cover the arbitrary field in `brownHypotheses`.
Source: blueprint sk-lem-brown-hypotheses, proof paragraphs 1--2. -/
private theorem brownHypotheses_finiteIntermediateField
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (F : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    BrownHypothesesFor (Profinite.continuousMapRingObj F) X := by
  classical
  let Λ := Profinite.continuousMapRingObj.{u} F
  let S := constantModelBoundedConstructible Λ X ⊓
    fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  let L := localizingClosureProEtale Λ X
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of D.k))
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of D.k))
  let A := ULift.{u} (ZMod 1)
  let _ : TopologicalSpace A := ⊥
  have hA : ∃ n : ℕ, (ℓ ^ n : A) = 0 := ⟨0, Subsingleton.elim _ _⟩
  have hS := det_brown_hypotheses_small ℓ A hA F Λ
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Iso.refl _⟩))))) X
  obtain ⟨J, hJ, ⟨e⟩⟩ := (ObjectProperty.exists_equivalence_iff S).mpr hS.2.2.2
  let _ := hJ
  let G := Skeleton J
  let H : G ⥤ S.FullSubcategory := fromSkeleton J ⋙ e.inverse
  let g : G → ConstantModelConstructibleFiniteTor Λ X := H.obj
  have hG (C : ConstantModelConstructibleFiniteTor Λ X) :
      ∃ i : G, Nonempty (C.obj ≅ (g i).obj) := by
    refine ⟨toSkeleton (e.functor.obj C), ⟨?_⟩⟩
    exact S.ι.mapIso (e.unitIso.app C ≪≫
      e.inverse.mapIso (fromSkeletonToSkeletonIso (e.functor.obj C)).symm)
  have hsk (i j : G) (h : Nonempty ((g i).obj ≅ (g j).obj)) : i = j := by
    obtain ⟨q⟩ := h
    exact skeleton_skeletal J ⟨H.preimageIso (S.isoMk q)⟩
  have hL (i : G) : L (g i).obj := fun _ _ hSP ↦ hSP _ (g i).property
  obtain ⟨hcop, hc⟩ := brownHypothesesFiniteFieldCompactness D ℓ hℓ X Λ
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨F, ⟨Iso.refl _⟩⟩))))) G g hG hsk
  let _ := hcop
  obtain ⟨hsmall, htri, hiso, hid, _⟩ := brownHypotheses_structural Λ X
  let _ := hsmall
  let _ := hid
  apply brownHypothesesFor_of_compact Λ X hS
  intro K hK
  obtain ⟨i, ⟨q⟩⟩ := hG ⟨K.obj, hK⟩
  exact compact_of_iso (L.isoMk q) (hc hL i)

/-- Brown representability hypotheses for a separated finite-type scheme in positive
characteristic different from the coefficient prime, for exactly the admissible rings.
`IsLocalizingAdmissibleCoefficient` specifies the six concrete coefficient objects up to
ring-object isomorphism, including the discrete finite rings killed by a power of `ℓ`.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-brown-hypotheses/_section.md and sk-lem-brown-hypotheses.proof.md
(blueprint: sk-lem-brown-hypotheses).

Proof: First unpack sk-def-sfb-dc-setting: the datum is a prime ℓ, a field of
characteristic p > 0 distinct from ℓ, and a separated finite-type k-scheme X.
Unpack sk-def-localizing-closure: Λ is one of the six specified condensed rings;
the ambient category is the unbounded derived category of modules over Λ_X;
S is the bounded constructible finite-Tor property and L is its replete localizing
intersection, with coproducts in the fixed universe and no completeness restriction.
Second apply det-brown-hypotheses-ambient to this datum to obtain local smallness,
triangulation, arbitrary sums and split idempotents of L. Apply
 det-brown-hypotheses-small to obtain thickness and essential smallness of S.
Choosing one representative per isomorphism class gives a small skeleton.
Third let G be any such skeleton and apply det-brown-hypotheses-generation:
each representative is compact in L, and vanishing of Hom(C[n], K) for all
representatives C and all integers n forces K to be zero. Compactness is exactly
def-pc-compact-object. To identify the second conclusion with def-pc-generators,
use Hom(coproduct C, K[-n]) = product Hom(C[n], K). If every morphism from the
coproduct into every shift of K is zero, the component Hom groups vanish,
so K is zero; contrapositively every nonzero K receives a nonzero map from the
coproduct into some shift. This is IsTriangulatedGeneratingFamily. All these
arguments apply to every small skeleton, with the inherited shift and any chosen
coproduct universal properties. -/
-- STATEMENT-DISPUTED: The arbitrary-field compactness assertion lacks a finiteness
-- hypothesis on the base field. The finite/rational compactness dependencies require
-- FiniteFieldDatum; the integral one requires an Ext bound. Finite type over an arbitrary
-- positive-characteristic field does not supply finite ℓ-cohomological dimension.
-- Generation itself is proved without this finiteness assumption by the helpers above.
-- The supplied compactness theorem specifically uses D.k, the algebraic closure of a
-- finite field. Its algebraic-closure coefficient is finite-subextension-valued; it
-- does not cover the separate all-continuous-map compatibility clause in hΛ.
-- The supported finite-intermediate-field Brown bundle is proved above.
theorem brownHypotheses
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    BrownHypothesesFor Λ X := by
  sorry

end CategoryTheory
