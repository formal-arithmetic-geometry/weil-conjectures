module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Triangulated.Generators
import all Sheaf.SixFunctors.BrownHypothesesSmall
import Sheaf.SixFunctorsBasics.BrownHypothesesStructural
import Sheaf.Paper.PadicConstantLocalModelTor
import Sheaf.Paper.StratifiedTorIntervalDevissage
import Sheaf.Paper.CohomologyTorInterval
import Sheaf.Paper.IntegralConstructibleCompactness
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import WeilConjectures.CategoryTheory.CompactObjectsThick
import WeilConjectures.CategoryTheory.DerivedCategory.Products
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi

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
set_option linter.all false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory

/-- Cache the canonical monoidal structure on condensed abelian groups.
This is the existing instance, with its site-size witnesses inferred once. -/
noncomputable abbrev brownHypothesesCondensedMonoidal :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  inferInstance

attribute [local instance 30000] brownHypothesesCondensedMonoidal

/-- Cache the canonical braiding on condensed abelian groups. -/
noncomputable abbrev brownHypothesesCondensedBraided :
    BraidedCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  inferInstance

attribute [local instance 30000] brownHypothesesCondensedBraided

/-- Cache the canonical monoidal structure on pro-etale abelian sheaves. -/
noncomputable abbrev brownHypothesesSheafMonoidal (X : Scheme.{u}) :
    MonoidalCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory Ab X

attribute [local instance 30000] brownHypothesesSheafMonoidal

/-- Cache the canonical braiding on pro-etale abelian sheaves. -/
noncomputable abbrev brownHypothesesSheafBraided (X : Scheme.{u}) :
    BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  AlgebraicGeometry.ProEtale.sheafBraidedCategory Ab X

attribute [local instance 30000] brownHypothesesSheafBraided

/-- Cache the existing ring-object structure pulled back from condensed coefficients. -/
noncomputable abbrev brownHypothesesCoefficientMonObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) : MonObj (condensedRingObj Λ X) :=
  Functor.monObjObj (F := upperStarFromPoint X) Λ

attribute [local instance 30000] brownHypothesesCoefficientMonObj

/-- Cache the existing closed tensor structure on pro-etale module objects. -/
noncomputable abbrev brownHypothesesModuleMonoidalClosed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    MonoidalClosed (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  inferInstance

attribute [local instance 30000] brownHypothesesModuleMonoidalClosed

-- Use the direct sheaf braiding when synthesizing the module-object tensor structure.
-- Reducing both the symmetric and braided localization constructions is expensive.
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar

/-- Exact countable products follow directly from repleteness and the exact forgetful
functor on module objects. Keep this proof local to avoid importing proper direct images. -/
private theorem brownHypotheses_countableAB4Star
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    CountableAB4Star (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
    Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)

attribute [local instance] brownHypotheses_countableAB4Star

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

private theorem isZero_of_shifted_orthogonal
    {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : ObjectProperty C) (K : C) (hK : localizingClosure S K)
    (horth : ∀ n : ℤ, S.rightOrthogonal (K⟦n⟧)) : IsZero K := by
  let P := (ObjectProperty.singleton K).shiftClosure ℤ
  have hP : IsLocalizingSubcategory P.leftOrthogonal := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I F hF hFP
    let := hF
    change P.leftOrthogonal (colimit F)
    intro Y f hY
    apply colimit.hom_ext
    intro j
    simpa using hFP j.as (colimit.ι F j ≫ f) hY
  have hSP : S ≤ P.leftOrthogonal := by
    intro M hM Y f hY
    obtain ⟨Z, n, e, hZ⟩ := hY
    have hZK : K = Z := (ObjectProperty.singleton_iff K Z).mp hZ
    subst Z
    apply (cancel_mono e.hom).mp
    simpa using horth n (f ≫ e.hom) hM
  have hid : (𝟙 K : K ⟶ K) = 0 :=
    hK P.leftOrthogonal hP hSP (𝟙 K)
      ((ObjectProperty.singleton K).le_shiftClosure K (by simp))
  exact (IsZero.iff_id_eq_zero K).mpr hid

/-- Any family representing every object of `S` up to isomorphism generates the
localizing closure of `S`. The property `S` need not be thick or shift-stable, and
the representatives need not be compact or pairwise nonisomorphic.

Source: blueprint latest, sec-six-functors-basics/sk-lem-brown-hypotheses,
proof paragraph 2 (blueprint: lem-sfb-localizing-closure-generators).

Proof: suppose all morphisms from the coproduct into every shift of `K` vanish.
Every map from one representative to a shift of `K` extends to the coproduct by
zero on the other summands. Thus every map from an object of `S` into a shift
of `K` vanishes. The left orthogonal of all shifts of `K` is replete,
triangulated, and closed under coproducts, since maps out of a coproduct are
determined by their components. It contains `S`, hence its localizing closure.
In particular it contains `K`, so the identity of `K` vanishes and `K` is zero.
Contraposition gives the stated nonzero-map generation criterion. -/
theorem localizingClosure_generatingFamily
    {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (S : ObjectProperty C) [hL : (localizingClosure S).IsTriangulated]
    {I : Type*} (E : I → (localizingClosure S).FullSubcategory) [HasCoproduct E]
    (hE : ∀ X : C, S X → ∃ i : I, Nonempty (X ≅ (E i).obj)) :
    IsTriangulatedGeneratingFamily E := by
  classical
  intro K hK
  by_contra! hn
  have horth : ∀ n : ℤ, S.rightOrthogonal (K.obj⟦n⟧) := by
    intro n X f hX
    obtain ⟨i, ⟨e⟩⟩ := hE X hX
    let q := ((localizingClosure S).ι.commShiftIso n).app K
    let a : E i ⟶ K⟦n⟧ := ObjectProperty.homMk (e.inv ≫ f ≫ q.inv)
    have ha : a = 0 := by
      have h := congrArg (fun g ↦ Sigma.ι E i ≫ g)
        (hn n (Limits.Sigma.desc (Pi.single (M := fun j ↦ E j ⟶ K⟦n⟧) i a)))
      simpa using h
    have h := congrArg (fun g ↦ e.hom ≫ g.hom ≫ q.hom) ha
    simpa [a] using h
  exact hK (IsZero.of_full_of_faithful_of_isZero (localizingClosure S).ι K
    (isZero_of_shifted_orthogonal S K.obj K.property horth))

/-- Compactness transports by precomposition with an isomorphism. -/
private theorem compact_of_iso
    {C : Type*} [Category.{u} C] [Preadditive C] [HasCoproducts.{u} C]
    {K L : C} (e : K ≅ L) (hL : IsCompactObject L) : IsCompactObject K := by
  exact (isCompactObject_iff_isCompactObj K).mpr
    (((isCompactObject_iff_isCompactObj L).mp hL).of_iso e)

/-- Brown's hypotheses reduce to thickness, essential smallness, and compactness of the
constructible finite-Tor objects. The ambient structures and generation follow formally
from the definition of the localizing closure, for every commutative condensed coefficient.

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraphs 1--2
(blueprint: lem-sfb-brown-hypotheses-criterion).

Proof: the forward direction uses essential smallness to choose a small equivalent
category of the constructible finite-Tor subcategory. Its representatives belong to the
localizing closure by minimality. The bundle makes them compact. Every constructible
finite-Tor object is isomorphic to a representative, so compactness transports to it.
For the reverse direction use the coefficient-independent structural theorem for local
smallness and split idempotents. The localizing intersection inherits its triangulation.
For any small presentation, compactness holds by the supplied objectwise assumption,
and the orthogonal/minimality argument proves generation. No assumption on a base field,
no skeletal condition, and no coefficient classification is used. -/
theorem brownHypothesesFor_iff
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    BrownHypothesesFor Λ X ↔
      let S := constantModelBoundedConstructible Λ X ⊓
        fun K ↦ DerivedCategory.finiteTorAmplitude _ K
      S.IsTriangulated ∧ S.IsClosedUnderIsomorphisms ∧ S.IsStableUnderRetracts ∧
        ObjectProperty.EssentiallySmall.{u + 1} S ∧
        ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
          letI := hSums
          ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
            S K.obj → IsCompactObject K := by
  classical
  let S := constantModelBoundedConstructible Λ X ⊓
    fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  let L := localizingClosureProEtale Λ X
  constructor
  · rintro ⟨hsmall, htri, hiso, hS, hSiso, hret, hess, hid, hcop, hgen⟩
    let _ := hsmall
    let _ := htri
    let _ := hcop
    refine ⟨hS, hSiso, hret, hess, hcop, ?_⟩
    obtain ⟨J, hJ, ⟨e⟩⟩ := (ObjectProperty.exists_equivalence_iff S).mpr hess
    let _ := hJ
    have hL (j : J) : L (e.inverse.obj j).obj :=
      fun _ _ hSP ↦ hSP _ (e.inverse.obj j).property
    have hc := (hgen J e.symm hL).1
    intro K hK
    let B : S.FullSubcategory := ⟨K.obj, hK⟩
    let K' : L.FullSubcategory :=
      ⟨(e.inverse.obj (e.functor.obj B)).obj, hL (e.functor.obj B)⟩
    let eK : K ≅ K' := L.isoMk (S.ι.mapIso (e.unitIso.app B))
    exact compact_of_iso eK (hc (e.functor.obj B))
  · rintro ⟨hS, hSiso, hret, hess, hcop, hc⟩
    obtain ⟨hsmall, htri, hiso, hid, _⟩ := brownHypotheses_structural Λ X
    let _ := hsmall
    let _ := htri
    let _ : (localizingClosure S).IsTriangulated := htri
    let _ : HasCoproducts.{u + 1} (localizingClosure S).FullSubcategory := hcop
    let _ := hid
    let _ := hcop
    refine ⟨hsmall, htri, hiso, hS, hSiso, hret, hess, hid, hcop, ?_⟩
    intro G _ e hL
    refine ⟨fun g ↦ hc _ (e.functor.obj g).property, ?_⟩
    have hsum : HasCoproduct (fun g : G ↦
        (⟨(e.functor.obj g).obj, hL g⟩ : L.FullSubcategory)) := inferInstance
    let _ := hsum
    apply localizingClosure_generatingFamily (E := fun g : G ↦
      (⟨(e.functor.obj g).obj, hL g⟩ : L.FullSubcategory)) S
    intro Y hY
    let B : S.FullSubcategory := ⟨Y, hY⟩
    exact ⟨e.inverse.obj B, ⟨(S.ι.mapIso (e.counitIso.app B)).symm⟩⟩

-- Later proofs use the criterion API; keep the large bundle folded.
attribute [local irreducible] BrownHypothesesFor

/-- Compactness in the Brown criterion can be checked on thick generators of the
constructible finite-Tor objects. The generators need not represent every isomorphism
class. The thick-envelope hypothesis is in the actual localizing full subcategory,
with its canonical inherited shift. Zero objects are adjoined to include empty families.

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraphs 1--2,
and Stacks Project, Tag 09QH (compact objects form a thick subcategory).
(blueprint: lem-sfb-brown-thick-generator-compactness-criterion).

Proof: the forward direction restricts the objectwise Brown criterion to the given
constructible finite-Tor generators. Conversely compact objects in the localizing
subcategory form a thick subcategory by Tag 09QH. They contain the generators and
all zero objects, hence their thick envelope. The covering hypothesis therefore
makes every constructible finite-Tor object compact. Combine this with the unchanged
thickness and essential-smallness clauses using the objectwise Brown criterion.
No compactness assertion for arbitrary fields is assumed or concluded. -/
theorem brownHypothesesFor_iff_compact_thick_generators
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [(localizingClosureProEtale Λ X).IsTriangulated]
    {G : Type*} (E : G → (localizingClosureProEtale Λ X).FullSubcategory)
    (hE : ∀ i, constantModelBoundedConstructible Λ X (E i).obj ∧
      DerivedCategory.finiteTorAmplitude _ (E i).obj)
    (hcover : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      (constantModelBoundedConstructible Λ X K.obj ∧
        DerivedCategory.finiteTorAmplitude _ K.obj) →
      (ObjectProperty.ofObj E ⊔ IsZero).triangEnvelope K) :
    BrownHypothesesFor Λ X ↔
      let S := constantModelBoundedConstructible Λ X ⊓
        fun K ↦ DerivedCategory.finiteTorAmplitude _ K
      S.IsTriangulated ∧ S.IsClosedUnderIsomorphisms ∧ S.IsStableUnderRetracts ∧
        ObjectProperty.EssentiallySmall.{u + 1} S ∧
        ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
          letI := hSums
          ∀ i, IsCompactObject (E i) := by
  constructor
  · intro hB
    obtain ⟨ht, hi, hr, hs, hcop, hc⟩ := (brownHypothesesFor_iff Λ X).mp hB
    exact ⟨ht, hi, hr, hs, hcop, fun i ↦ hc (E i) (hE i)⟩
  · rintro ⟨ht, hi, hr, hs, hcop, hc⟩
    let _ := hcop
    let R : ObjectProperty (localizingClosureProEtale Λ X).FullSubcategory :=
      fun K ↦ IsCompactObject K
    obtain ⟨hRt, hRr⟩ := compactObjects_isThick
      (C := (localizingClosureProEtale Λ X).FullSubcategory)
    let _ : R.IsTriangulated := hRt
    let _ : R.IsStableUnderRetracts := hRr
    have hR : (ObjectProperty.ofObj E ⊔ IsZero).triangEnvelope ≤ R := by
      apply (ObjectProperty.triangEnvelope_le_iff
        (ObjectProperty.ofObj E ⊔ IsZero) (Q := R)).mpr
      intro K hK
      rcases hK with hK | hK
      · obtain ⟨i⟩ := hK
        exact hc i
      · exact R.prop_of_isZero hK
    exact (brownHypothesesFor_iff Λ X).mpr
      ⟨ht, hi, hr, hs, hcop, fun K hK ↦ hR K (hcover K hK)⟩

/-- Brown compactness can be tested on any family representing the constructible
finite-Tor objects. The family needs neither a category structure nor a skeletal
condition, and its indexing universe need not be the coproduct indexing universe.
Thickness and essential smallness remain explicit clauses of the criterion.

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraphs 1--2,
compact representatives and transport along isomorphisms
(blueprint: lem-sfb-brown-representative-compactness-criterion).

Proof: the forward objectwise criterion makes every representative compact for
any proof of its membership in the closure. Conversely each constructible finite-Tor
object is isomorphic to a representative. Both objects lie in the full closure,
so the isomorphism lifts to that category and transports compactness back to the
original object. Apply the objectwise criterion to obtain the Brown bundle;
its orthogonal argument supplies generation. Repeated representatives and an empty
family are allowed: in the latter case the covering hypothesis makes the
constructible finite-Tor category empty as well. -/
theorem brownHypothesesFor_iff_compact_representatives
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {G : Type*} (g : G → ConstantModelConstructibleFiniteTor Λ X)
    (hG : ∀ C : ConstantModelConstructibleFiniteTor Λ X,
      ∃ i : G, Nonempty (C.obj ≅ (g i).obj)) :
    BrownHypothesesFor Λ X ↔
      let S := constantModelBoundedConstructible Λ X ⊓
        fun K ↦ DerivedCategory.finiteTorAmplitude _ K
      S.IsTriangulated ∧ S.IsClosedUnderIsomorphisms ∧ S.IsStableUnderRetracts ∧
        ObjectProperty.EssentiallySmall.{u + 1} S ∧
        ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
          letI := hSums
          ∀ (hL : ∀ i, localizingClosureProEtale Λ X (g i).obj) (i : G),
            IsCompactObject (⟨(g i).obj, hL i⟩ :
              (localizingClosureProEtale Λ X).FullSubcategory) := by
  let L := localizingClosureProEtale Λ X
  have hL (i : G) : L (g i).obj := fun _ _ hSP ↦ hSP _ (g i).property
  let E : G → L.FullSubcategory := fun i ↦ ⟨(g i).obj, hL i⟩
  obtain ⟨_, htri, _, _, _⟩ := brownHypotheses_structural Λ X
  let _ := htri
  have hcover (K : L.FullSubcategory)
      (hK : constantModelBoundedConstructible Λ X K.obj ∧
        DerivedCategory.finiteTorAmplitude _ K.obj) :
      (ObjectProperty.ofObj E ⊔ IsZero).triangEnvelope K := by
    obtain ⟨i, ⟨q⟩⟩ := hG ⟨K.obj, hK⟩
    exact ((ObjectProperty.ofObj E ⊔ IsZero).triangEnvelope).prop_of_iso
      (L.isoMk q).symm
      ((ObjectProperty.ofObj E ⊔ IsZero).le_triangEnvelope _
        (Or.inl (ObjectProperty.ofObj_apply E i)))
  have criterion := brownHypothesesFor_iff_compact_thick_generators Λ X E
    (fun i ↦ (g i).property) hcover
  constructor
  · intro hB
    obtain ⟨ht, hi, hr, hs, hcop, hc⟩ := criterion.mp hB
    refine ⟨ht, hi, hr, hs, hcop, ?_⟩
    intro hL' i
    exact hc i
  · rintro ⟨ht, hi, hr, hs, hcop, hc⟩
    exact criterion.mpr ⟨ht, hi, hr, hs, hcop, hc hL⟩

private theorem finite_nonzero_hom_of_compact_product_coproduct
    {C : Type*} [Category.{u + 1} C] [Preadditive C] [HasCoproducts.{u + 1} C]
    (K : C) (hK : IsCompactObject K)
    {I : Type (u + 1)} (E : I → C)
    (c : Cofan E) (hc : IsColimit c) (π : ∀ i, c.pt ⟶ E i)
    (hp : IsLimit (Fan.mk c.pt π))
    (hdiag : ∀ i j, i ≠ j → c.inj i ≫ π j = 0) :
    ∃ S : Finset I, ∀ i ∉ S, Subsingleton (K ⟶ E i) := by
  classical
  have hfinite := (isCompactObject_iff_isCompactObj K).mp hK
  have hchoice (i : I) : ∃ f : K ⟶ E i, ∀ g : K ⟶ E i, f = 0 → g = 0 := by
    by_cases h : ∀ g : K ⟶ E i, g = 0
    · exact ⟨0, fun g _ ↦ h g⟩
    · obtain ⟨f, hf⟩ := not_forall.mp h
      exact ⟨f, fun _ hz ↦ (hf hz).elim⟩
  choose f hf using hchoice
  obtain ⟨S, g, hg⟩ := hfinite c hc (Fan.IsLimit.lift hp f)
  refine ⟨S, fun i hi ↦ ?_⟩
  have hz : Fan.IsLimit.lift hp f ≫ π i = 0 := by
    rw [hg, Preadditive.sum_comp]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Category.assoc, hdiag j i (ne_of_mem_of_not_mem hj hi), comp_zero]
  have hfi : f i = 0 := (Fan.IsLimit.fac hp f i).symm.trans hz
  exact ⟨fun a b ↦ (hf i a hfi).trans (hf i b hfi).symm⟩


/-- A Brown bundle forces finite support of Hom groups into a family whose coproduct
is also its product, with the usual diagonal projections.

Source: the finite-support compactness obstruction in
`WeilConjectures.CategoryTheory.DerivedCategory.NotPreservesCoproducts`, applied to the
constructible finite-Tor compactness clause of the Brown bundle.
(blueprint: lem-sfb-brown-product-coproduct-obstruction).

Proof: choose one map into each summand, nonzero whenever its Hom group is nonzero.
The product property combines these maps into one map to the coproduct. Compactness
expresses this map as a finite sum through the coproduct injections. Composing with
any projection outside that finite set gives zero, because all off-diagonal composites
vanish. The product identities say that the chosen component is zero. By its choice,
every map into that summand is zero. This is a conditional obstruction only: no field
cohomology calculation or unconditional counterexample is asserted. -/
theorem BrownHypothesesFor.finite_nonzero_hom_of_product_coproduct
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (hB : BrownHypothesesFor Λ X)
    (K : (localizingClosureProEtale Λ X).FullSubcategory)
    (hK : constantModelBoundedConstructible Λ X K.obj ∧
      DerivedCategory.finiteTorAmplitude _ K.obj)
    {I : Type (u + 1)} (E : I → (localizingClosureProEtale Λ X).FullSubcategory)
    (c : Cofan E) (hc : IsColimit c) (π : ∀ i, c.pt ⟶ E i)
    (hp : IsLimit (Fan.mk c.pt π))
    (hdiag : ∀ i j, i ≠ j → c.inj i ≫ π j = 0) :
    ∃ S : Finset I, ∀ i ∉ S, Subsingleton (K ⟶ E i) := by
  obtain ⟨_, _, _, _, hcop, hcompact⟩ := (brownHypothesesFor_iff Λ X).mp hB
  let _ := hcop
  exact finite_nonzero_hom_of_compact_product_coproduct K (hcompact K hK) E c hc π hp hdiag

/-- An infinite family of nonzero Hom groups into a coproduct which is also a product
obstructs the Brown bundle.

Source: `WeilConjectures.CategoryTheory.DerivedCategory.NotPreservesCoproducts`,
finite-support obstruction, and the Brown-hypotheses compactness clause.
(blueprint: lem-sfb-brown-product-coproduct-obstruction).

Proof: Brown's bundle and the preceding theorem give a finite set outside which every
Hom group is zero. An infinite set of indices supporting a nonzero map cannot be
contained in that finite set. At an index outside it, the chosen nonzero map equals
zero by subsingleton elimination, a contradiction. -/
theorem not_brownHypothesesFor_of_product_coproduct
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (K : (localizingClosureProEtale Λ X).FullSubcategory)
    (hK : constantModelBoundedConstructible Λ X K.obj ∧
      DerivedCategory.finiteTorAmplitude _ K.obj)
    {I : Type (u + 1)} (E : I → (localizingClosureProEtale Λ X).FullSubcategory)
    (c : Cofan E) (hc : IsColimit c) (π : ∀ i, c.pt ⟶ E i)
    (hp : IsLimit (Fan.mk c.pt π))
    (hdiag : ∀ i j, i ≠ j → c.inj i ≫ π j = 0)
    (hhom : {i : I | ∃ f : K ⟶ E i, f ≠ 0}.Infinite) :
    ¬ BrownHypothesesFor Λ X := by
  intro hB
  obtain ⟨S, hS⟩ := hB.finite_nonzero_hom_of_product_coproduct K hK E c hc π hp hdiag
  obtain ⟨i, ⟨f, hf⟩, hi⟩ := hhom.exists_notMem_finset S
  exact hf ((hS i hi).elim f 0)

open scoped CategoryTheory.Obj in
private theorem finite_nonzero_hom_of_compact_degreewise_disjoint
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    [HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory]
    (K : (localizingClosureProEtale Λ X).FullSubcategory)
    (hK : IsCompactObject K)
    (M : ℕ → CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (hM : ∀ n, localizingClosureProEtale Λ X (DerivedCategory.Q.obj (M n)))
    (hdisjoint : ∀ (d : ℤ) (m n : ℕ),
      ¬ IsZero ((M m).X d) → ¬ IsZero ((M n).X d) → m = n) :
    ∃ S : Finset ℕ, ∀ n ∉ S, Subsingleton (K.obj ⟶ DerivedCategory.Q.obj (M n)) := by
  classical
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let L := localizingClosureProEtale Λ X
  obtain ⟨_, htri, hiso, _, hcop, _⟩ := brownHypotheses_structural Λ X
  let _ := htri
  let _ := hiso
  let _ := hcop
  have hs := coproductIsCoproduct M
  let p := Cofan.IsColimit.proj hs
  have hc := DerivedCategory.isColimitCofanMkQObj hs
  have hp := DerivedCategory.isLimitFanMkQObj
    (HomologicalComplex.isLimitFanMkProjOfIsColimit hdisjoint hs)
  have hpt : L (DerivedCategory.Q.obj (∐ M)) := by
    intro P hP hSP
    let _ := hP.2.1
    let c : Cofan (fun n : ULift.{u + 2} ℕ ↦ DerivedCategory.Q.obj (M n.down)) :=
      Cofan.mk _ (fun n ↦ DerivedCategory.Q.map (Sigma.ι M n.down))
    have hcc : IsColimit c :=
      (Cofan.isColimitEquivOfEquiv Equiv.ulift _).toFun hc
    let _ : HasColimit (Discrete.functor
      (fun n : ULift.{u + 2} ℕ ↦ DerivedCategory.Q.obj (M n.down))) := ⟨_, hcc⟩
    let D := Discrete.functor
      (fun n : ULift.{u + 2} ℕ ↦ DerivedCategory.Q.obj (M n.down))
    have hmem := hP.2.2 D inferInstance (fun n ↦ hM n.down P hP hSP)
    exact P.prop_of_iso ((colimit.isColimit D).coconePointUniqueUpToIso hcc) hmem
  let E (n : ULift.{u + 1} ℕ) : L.FullSubcategory := ⟨_, hM n.down⟩
  let B : L.FullSubcategory := ⟨_, hpt⟩
  let c : Cofan E := Cofan.mk B (fun n ↦
    ObjectProperty.homMk (DerivedCategory.Q.map (Sigma.ι M n.down)))
  let π (n : ULift.{u + 1} ℕ) : B ⟶ E n :=
    ObjectProperty.homMk (DerivedCategory.Q.map (p n.down))
  have hc' : IsColimit c := by
    refine Cofan.IsColimit.mk _ (fun s ↦ ObjectProperty.homMk
      (Cofan.IsColimit.desc hc (fun n ↦ (s.inj ⟨n⟩).hom))) ?_ ?_
    · intro s n
      apply ObjectProperty.hom_ext
      exact Cofan.IsColimit.fac hc (fun n ↦ (s.inj ⟨n⟩).hom) n.down
    · intro s f hf
      apply ObjectProperty.hom_ext
      apply Cofan.IsColimit.hom_ext hc
      intro n
      exact (congrArg (fun f ↦ f.hom) (hf ⟨n⟩)).trans
        (Cofan.IsColimit.fac hc (fun n ↦ (s.inj ⟨n⟩).hom) n).symm
  have hp' : IsLimit (Fan.mk B π) := by
    refine Fan.IsLimit.mk _ (fun s ↦ ObjectProperty.homMk
      (Fan.IsLimit.lift hp (fun n ↦ (s.proj ⟨n⟩).hom))) ?_ ?_
    · intro s n
      apply ObjectProperty.hom_ext
      exact Fan.IsLimit.fac hp (fun n ↦ (s.proj ⟨n⟩).hom) n.down
    · intro s f hf
      apply ObjectProperty.hom_ext
      apply Fan.IsLimit.hom_ext hp
      intro n
      exact (congrArg (fun f ↦ f.hom) (hf ⟨n⟩)).trans
        (Fan.IsLimit.fac hp (fun n ↦ (s.proj ⟨n⟩).hom) n).symm
  obtain ⟨S, hS⟩ := finite_nonzero_hom_of_compact_product_coproduct K hK E c hc' π hp'
    (fun i j hij ↦ by
      apply ObjectProperty.hom_ext
      have hne : i.down ≠ j.down := fun h ↦ hij (ULift.ext _ _ h)
      simpa [c, π, p, ← Functor.map_comp] using
        congrArg DerivedCategory.Q.map (Cofan.IsColimit.inj_proj_of_ne hs hne))
  refine ⟨S.image ULift.down, fun n hn ↦ ?_⟩
  have hnS : (ULift.up n : ULift.{u + 1} ℕ) ∉ S := by
    exact fun h ↦ hn (Finset.mem_image.mpr ⟨_, h, rfl⟩)
  refine ⟨fun f g ↦ ?_⟩
  exact congrArg (fun h : K ⟶ E ⟨n⟩ ↦ h.hom)
    ((hS _ hnS).elim (ObjectProperty.homMk f) (ObjectProperty.homMk g))


open scoped CategoryTheory.Obj in
/-- Brown compactness forces finite Hom support into degreewise disjoint complexes.
The complexes may have several nonzero terms and need not be bounded or constructible.
Only their derived images must belong to the localizing closure.

Source: the finite-support argument in
`WeilConjectures.CategoryTheory.DerivedCategory.NotPreservesCoproducts`, using
`HomologicalComplex.isLimitFanMkProjOfIsColimit` from `DegreewiseLimits`.
(blueprint: lem-sfb-brown-disjoint-complex-hom-support).

Proof: form the termwise coproduct of the complexes. In each degree at most one
summand is nonzero, so the canonical projections also make it their product.
Exact countable products of pro-etale module objects transport this product to
the derived category; the derived localization preserves the coproduct as well.
The localizing intersection contains that coproduct because it contains each
summand. Fullness restricts both universal properties to the localizing category.
The Brown finite-support theorem applies there. Passing through the full inclusion
and lowering the lifted natural-number indices gives the asserted finite set. -/
theorem BrownHypothesesFor.finite_nonzero_hom_of_degreewise_disjoint
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (hB : BrownHypothesesFor Λ X)
    (K : (localizingClosureProEtale Λ X).FullSubcategory)
    (hK : constantModelBoundedConstructible Λ X K.obj ∧
      DerivedCategory.finiteTorAmplitude _ K.obj)
    (M : ℕ → CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (hM : ∀ n, localizingClosureProEtale Λ X (DerivedCategory.Q.obj (M n)))
    (hdisjoint : ∀ (d : ℤ) (m n : ℕ),
      ¬ IsZero ((M m).X d) → ¬ IsZero ((M n).X d) → m = n) :
    ∃ S : Finset ℕ, ∀ n ∉ S, Subsingleton (K.obj ⟶ DerivedCategory.Q.obj (M n)) := by
  obtain ⟨_, _, _, _, hcop, hcompact⟩ := (brownHypothesesFor_iff Λ X).mp hB
  let _ := hcop
  exact finite_nonzero_hom_of_compact_degreewise_disjoint K (hcompact K hK) M hM hdisjoint

open scoped CategoryTheory.Obj in
private theorem eventually_hom_single_shift_eq_zero_of_compact
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    [HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory]
    (K : (localizingClosureProEtale Λ X).FullSubcategory)
    (hK : IsCompactObject K)
    (F : ℕ → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : ∀ n, localizingClosureProEtale Λ X
      ((DerivedCategory.singleFunctor _ 0).obj (F n))) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f : K.obj ⟶
      ((DerivedCategory.singleFunctor _ 0).obj (F n))⟦(n : ℤ)⟧, f = 0 := by
  classical
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let M (n : ℕ) := ((CochainComplex.singleFunctor A 0).obj (F n))⟦(n : ℤ)⟧
  obtain ⟨_, htri, hiso, _, _, _⟩ := brownHypotheses_structural Λ X
  let _ := htri
  let _ := hiso
  let e (n : ℕ) : DerivedCategory.Q.obj (M n) ≅
      ((DerivedCategory.singleFunctor A 0).obj (F n))⟦(n : ℤ)⟧ :=
    ((DerivedCategory.Q (C := A)).commShiftIso (n : ℤ)).app
        ((CochainComplex.singleFunctor A 0).obj (F n)) ≪≫
      (shiftFunctor _ (n : ℤ)).mapIso ((DerivedCategory.singleFunctorIsoCompQ A 0).app (F n)).symm
  have hm (n : ℕ) : localizingClosureProEtale Λ X (DerivedCategory.Q.obj (M n)) :=
    (localizingClosureProEtale Λ X).prop_of_iso (e n).symm
      ((localizingClosureProEtale Λ X).le_shift (n : ℤ) _ (hF n))
  have hdisjoint (d : ℤ) (m n : ℕ)
      (hm : ¬ IsZero ((M m).X d)) (hn : ¬ IsZero ((M n).X d)) : m = n := by
    have hdegree (j : ℕ) (hj : ¬ IsZero ((M j).X d)) : d + j = 0 := by
      by_contra h
      exact hj (HomologicalComplex.isZero_single_obj_X (.up ℤ) _ _ _ h)
    have := hdegree m hm
    have := hdegree n hn
    omega
  obtain ⟨S, hS⟩ := finite_nonzero_hom_of_compact_degreewise_disjoint K hK M hm hdisjoint
  refine ⟨S.sup id + 1, fun n hn f ↦ ?_⟩
  have hnS : n ∉ S := fun h ↦ by
    have hle : n ≤ S.sup id := Finset.le_sup (f := id) h
    omega
  have hz : f ≫ (e n).inv = 0 := (hS n hnS).elim _ _
  simpa using congrArg (fun g ↦ g ≫ (e n).hom) hz


open scoped CategoryTheory.Obj in
/-- Brown compactness forces eventual vanishing along any sequence of shifted heart objects.
The heart object may vary with the shift; only its membership in the closure is required.

Source: `WeilConjectures.CategoryTheory.DerivedCategory.NotPreservesCoproducts`,
finite-support argument, and `HomologicalComplex.isLimitFanMkProjOfIsColimit`.
(blueprint: lem-sfb-brown-varying-heart-ext-bound).

Proof: the nth complex is F_n[0][n]. In any fixed degree at most one is nonzero,
so the cochain coproduct is also a product. Exact countable products transport the
product property to the derived category. Both universal properties restrict to the
localizing closure, since it contains all shifted summands and their coproduct.
The finite-support theorem for the Brown bundle makes all Hom groups outside a
finite set zero. Any natural number larger than its indices is the desired bound.
This includes zero objects and arbitrary repetitions among the unshifted F_n. -/
theorem BrownHypothesesFor.eventually_hom_single_shift_eq_zero
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (hB : BrownHypothesesFor Λ X)
    (K : (localizingClosureProEtale Λ X).FullSubcategory)
    (hK : constantModelBoundedConstructible Λ X K.obj ∧
      DerivedCategory.finiteTorAmplitude _ K.obj)
    (F : ℕ → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : ∀ n, localizingClosureProEtale Λ X
      ((DerivedCategory.singleFunctor _ 0).obj (F n))) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f : K.obj ⟶
      ((DerivedCategory.singleFunctor _ 0).obj (F n))⟦(n : ℤ)⟧, f = 0 := by
  obtain ⟨_, _, _, _, hcop, hcompact⟩ := (brownHypothesesFor_iff Λ X).mp hB
  let _ := hcop
  exact eventually_hom_single_shift_eq_zero_of_compact K (hcompact K hK) F hF

open scoped CategoryTheory.Obj in
/-- A compact object of the localizing closure has a uniform bound on maps to shifted
heart objects in that closure. No constructibility or Brown bundle is assumed for K.

Source: the finite-support argument in
`WeilConjectures.CategoryTheory.DerivedCategory.NotPreservesCoproducts.lean`.
(blueprint: lem-sfb-compact-uniform-heart-ext-bound).

Proof: degreewise disjoint shifted single complexes have a coproduct which is also
their product, since countable products of pro-etale module objects are exact.
Compactness of K forces finite support of its maps to the summands. If some heart
object supports a nonzero map in arbitrarily high degrees, choose such an object
in each degree where possible (and a fixed eligible object otherwise). Finite
support for this varying sequence gives a contradiction. If there is no eligible
heart object, the bound zero works vacuously. The source K may itself be unbounded. -/
theorem exists_uniform_hom_single_shift_bound_of_compact
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    [HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory]
    (K : (localizingClosureProEtale Λ X).FullSubcategory)
    (hK : IsCompactObject K) :
    ∃ N : ℕ, ∀ F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X),
      localizingClosureProEtale Λ X ((DerivedCategory.singleFunctor _ 0).obj F) →
      ∀ n ≥ N, ∀ f : K.obj ⟶
        ((DerivedCategory.singleFunctor _ 0).obj F)⟦(n : ℤ)⟧, f = 0 := by
  classical
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let L := localizingClosureProEtale Λ X
  by_cases hex : ∃ F : A, L ((DerivedCategory.singleFunctor A 0).obj F)
  · obtain ⟨F₀, hF₀⟩ := hex
    let P (n : ℕ) := ∃ F : A, L ((DerivedCategory.singleFunctor A 0).obj F) ∧
      ∃ f : K.obj ⟶ ((DerivedCategory.singleFunctor A 0).obj F)⟦(n : ℤ)⟧, f ≠ 0
    let F (n : ℕ) : A := if h : P n then h.choose else F₀
    have hF (n : ℕ) : L ((DerivedCategory.singleFunctor A 0).obj (F n)) := by
      dsimp only [F]
      split_ifs with h
      · exact h.choose_spec.1
      · exact hF₀
    obtain ⟨N, hN⟩ := eventually_hom_single_shift_eq_zero_of_compact K hK F hF
    refine ⟨N, fun M hM n hn f ↦ ?_⟩
    by_contra hf
    have hp : P n := ⟨M, hM, f, hf⟩
    obtain ⟨g, hg⟩ := hp.choose_spec.2
    have hz := hN n hn
    change ∀ g : K.obj ⟶
      ((DerivedCategory.singleFunctor A 0).obj (F n))⟦(n : ℤ)⟧, g = 0 at hz
    rw [show F n = hp.choose from dif_pos hp] at hz
    exact hg (hz g)
  · exact ⟨0, fun F hF ↦ (hex ⟨F, hF⟩).elim⟩


open scoped CategoryTheory.Obj in
/-- Unbounded maps to shifted heart objects detect a noncompact source object directly.
Source: the finite-support argument of `DerivedCategory.NotPreservesCoproducts`.
(blueprint: lem-sfb-compact-uniform-heart-ext-bound).

Proof: compactness gives a uniform bound by the preceding theorem. Choose a nonzero
map in a degree at least that bound. The bound makes this map zero, a contradiction.
Neither constructibility of the source nor compactness of other objects is needed. -/
theorem not_isCompactObject_of_unbounded_ext
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    [HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory]
    (K : (localizingClosureProEtale Λ X).FullSubcategory)
    (hExt : ∀ N : ℕ, ∃ (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)),
      localizingClosureProEtale Λ X ((DerivedCategory.singleFunctor _ 0).obj F) ∧
      ∃ n ≥ N, ∃ f : K.obj ⟶
        ((DerivedCategory.singleFunctor _ 0).obj F)⟦(n : ℤ)⟧, f ≠ 0) :
    ¬ IsCompactObject K := by
  intro hK
  obtain ⟨N, hN⟩ := exists_uniform_hom_single_shift_bound_of_compact K hK
  obtain ⟨F, hF, n, hn, f, hf⟩ := hExt N
  exact hf (hN F hF n hn f)

open scoped CategoryTheory.Obj in
/-- The Ext bound forced by the Brown bundle is uniform over heart objects in the closure.

Source: the finite-support compactness argument of
`WeilConjectures.CategoryTheory.DerivedCategory.NotPreservesCoproducts`.
(blueprint: lem-sfb-brown-uniform-heart-ext-bound).

Proof: if the closure contains no degree-zero heart object the assertion is vacuous.
Otherwise fix one as a default. In each degree choose a heart object with a nonzero
Hom group when one exists, and use the default otherwise. The varying-heart bound
applied to this sequence rules out every nonzero Hom group in sufficiently high
degrees. The choices occur only in this proof; no coefficient object is redefined. -/
theorem BrownHypothesesFor.exists_uniform_hom_single_shift_bound
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (hB : BrownHypothesesFor Λ X)
    (K : (localizingClosureProEtale Λ X).FullSubcategory)
    (hK : constantModelBoundedConstructible Λ X K.obj ∧
      DerivedCategory.finiteTorAmplitude _ K.obj) :
    ∃ N : ℕ, ∀ F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X),
      localizingClosureProEtale Λ X ((DerivedCategory.singleFunctor _ 0).obj F) →
      ∀ n ≥ N, ∀ f : K.obj ⟶
        ((DerivedCategory.singleFunctor _ 0).obj F)⟦(n : ℤ)⟧, f = 0 := by
  obtain ⟨_, _, _, _, hcop, hcompact⟩ := (brownHypothesesFor_iff Λ X).mp hB
  let _ := hcop
  exact exists_uniform_hom_single_shift_bound_of_compact K (hcompact K hK)

open scoped CategoryTheory.Obj in
/-- Unbounded Ext into heart objects of the closure contradicts Brown's hypotheses.

Source: the finite-support compactness argument of
`WeilConjectures.CategoryTheory.DerivedCategory.NotPreservesCoproducts`.
(blueprint: lem-sfb-brown-uniform-heart-ext-bound).

Proof: the preceding uniform bound applies to every eligible heart object. Choose
from the unboundedness hypothesis a degree at least this bound and a nonzero map
in that degree. The bound makes this map zero, giving a contradiction. -/
theorem not_brownHypothesesFor_of_unbounded_ext
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (K : (localizingClosureProEtale Λ X).FullSubcategory)
    (hK : constantModelBoundedConstructible Λ X K.obj ∧
      DerivedCategory.finiteTorAmplitude _ K.obj)
    (hExt : ∀ N : ℕ, ∃ (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)),
      localizingClosureProEtale Λ X ((DerivedCategory.singleFunctor _ 0).obj F) ∧
      ∃ n ≥ N, ∃ f : K.obj ⟶
        ((DerivedCategory.singleFunctor _ 0).obj F)⟦(n : ℤ)⟧, f ≠ 0) :
    ¬ BrownHypothesesFor Λ X := by
  intro hB
  obtain ⟨_, _, _, _, hcop, hcompact⟩ := (brownHypothesesFor_iff Λ X).mp hB
  let _ := hcop
  exact not_isCompactObject_of_unbounded_ext K hExt (hcompact K hK)

open scoped CategoryTheory.Obj in
/-- Nonzero maps to every positive shift of a heart object in the localizing closure
obstruct the Brown bundle.

Source: `WeilConjectures.CategoryTheory.DerivedCategory.NotPreservesCoproducts`,
together with exact countable products of pro-etale module objects.
(blueprint: lem-sfb-brown-positive-ext-obstruction).

Proof: the complexes F[0][n] lie in pairwise distinct degrees, so their cochain coproduct
is also their product. Exact countable products and K-injective resolutions transport
both universal properties to the derived category. The localizing closure contains
every shift and their coproduct, so the universal properties restrict to it. Brown
compactness then forces all maps into sufficiently high members of this family to
vanish. This contradicts the supplied nonzero map to every positive shift. -/
theorem not_brownHypothesesFor_of_positive_ext
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (K : (localizingClosureProEtale Λ X).FullSubcategory)
    (hK : constantModelBoundedConstructible Λ X K.obj ∧
      DerivedCategory.finiteTorAmplitude _ K.obj)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : localizingClosureProEtale Λ X ((DerivedCategory.singleFunctor _ 0).obj F))
    (hExt : ∀ n : ℕ, ∃ f : K.obj ⟶
      ((DerivedCategory.singleFunctor _ 0).obj F)⟦((n + 1 : ℕ) : ℤ)⟧, f ≠ 0) :
    ¬ BrownHypothesesFor Λ X := by
  intro hB
  obtain ⟨N, hN⟩ := hB.eventually_hom_single_shift_eq_zero K hK (fun _ ↦ F)
    (fun _ ↦ hF)
  obtain ⟨f, hf⟩ := hExt N
  exact hf (hN (N + 1) (by omega) f)

/-- Lifting a finite discrete coefficient carrier preserves its condensed ring object. -/
private theorem finiteCoefficientLiftIso (A : Type) [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] :
    Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj (ULift.{u} A))) := by
  let ei : A ≃+* ULift.{u} A := ULift.ringEquiv.symm
  have hc : Continuous ei := continuous_of_discreteTopology
  have hc' : Continuous ei.symm := continuous_of_discreteTopology
  let er : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} A) :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hc).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop hc').comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.symm_apply_apply (f.down x)
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.apply_symm_apply (f.down x) }
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ er.hom
  exact ⟨Mon.mkIso ea⟩

/-- Admissibility supplies the thickness and size clauses independently of compactness. -/
private theorem brownHypotheses_admissible_small
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X] :
    let S := constantModelBoundedConstructible Λ X ⊓
      fun K ↦ DerivedCategory.finiteTorAmplitude _ K
    S.IsTriangulated ∧ S.IsClosedUnderIsomorphisms ∧ S.IsStableUnderRetracts ∧
      ObjectProperty.EssentiallySmall.{u + 1} S := by
  classical
  let A₀ := ULift.{u} (ZMod 1)
  let _ : TopologicalSpace A₀ := ⊥
  have hA₀ : ∃ n : ℕ, (ℓ ^ n : A₀) = 0 := ⟨0, Subsingleton.elim _ _⟩
  let F₀ : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  rcases hΛ with h | h | h | h | h | h
  · obtain ⟨A, _, _, _, _, hA, ⟨r, hr⟩, ⟨e⟩⟩ := h
    let _ := hA
    have hpow : ∃ n : ℕ, (ℓ ^ n : ULift.{u} A) = 0 := by
      refine ⟨r, ?_⟩
      apply ULift.ext
      simpa using hr 1
    obtain ⟨ea⟩ := finiteCoefficientLiftIso.{u} A
    exact det_brown_hypotheses_small ℓ (ULift.{u} A) hpow F₀ Λ
      (Or.inl ⟨e ≪≫ ea⟩) X
  · exact det_brown_hypotheses_small ℓ A₀ hA₀ F₀ Λ (Or.inr (Or.inl h)) X
  · exact det_brown_hypotheses_small ℓ A₀ hA₀ F₀ Λ
      (Or.inr (Or.inr (Or.inr (Or.inl h)))) X
  · obtain ⟨F, h⟩ := h
    exact det_brown_hypotheses_small ℓ A₀ hA₀ F Λ
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) X
  · obtain ⟨F, h⟩ := h
    exact det_brown_hypotheses_small ℓ A₀ hA₀ F Λ
      (Or.inr (Or.inr (Or.inl h))) X
  · exact det_brown_hypotheses_small ℓ A₀ hA₀ F₀ Λ
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))) X


/-- For a Noetherian scheme, admissibility leaves only compactness to check.
No field, characteristic, or separatedness hypothesis is required for this equivalence.

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraphs 1--2,
and det-brown-hypotheses-small, whose hypothesis is that X is Noetherian.
(blueprint: lem-sfb-brown-noetherian-compactness-criterion).

Proof: apply brownHypotheses_admissible_small to the actual admissibility predicate.
This supplies thickness and essential smallness
on any compact locally Noetherian scheme. The formal Brown criterion then extracts
compactness in one direction and assembles the bundle in the other direction.
The structural and generation clauses need no additional geometric hypothesis. -/
theorem brownHypothesesFor_iff_compact_of_noetherian
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    BrownHypothesesFor Λ X ↔
      ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
        letI := hSums
        ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
          (constantModelBoundedConstructible Λ X K.obj ∧
            DerivedCategory.finiteTorAmplitude _ K.obj) → IsCompactObject K := by
  have hsmall := brownHypotheses_admissible_small ℓ Λ hΛ X
  constructor
  · intro hB
    exact ((brownHypothesesFor_iff Λ X).mp hB).2.2.2.2
  · intro hc
    exact (brownHypothesesFor_iff Λ X).mpr
      ⟨hsmall.1, hsmall.2.1, hsmall.2.2.1, hsmall.2.2.2, hc⟩


/-- On a finite-type scheme over a field, only objectwise compactness remains to be
proved for Brown's bundle with admissible coefficients. This equivalence requires no
restriction on the characteristic or cohomological dimension of the base field, and
asserts no compactness theorem for that field. The explicit six-case coefficient
hypothesis is the one used by the finite-field compactness declaration.

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraphs 1--2,
using det-brown-hypotheses-small for the first paragraph and the formal Brown criterion
for the second (blueprint: lem-sfb-brown-admissible-compactness-criterion).

Proof: finite type over a field makes the scheme compact and locally Noetherian.
For each admissible coefficient apply the thickness and essential-smallness theorem.
Lift a finite discrete coefficient carrier from Type 0 to Type u using the explicit
continuous ring-object isomorphism; use the zero finite ring and bottom extension for
unused parameters in the other cases. The forward direction of the formal Brown
criterion extracts coproducts and objectwise compactness. Its reverse direction
assembles the bundle from the proved thickness and size clauses and the supplied
compactness. All coproducts use the same fixed indexing universe as the bundle. -/
theorem brownHypothesesFor_iff_compact_of_admissible
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ r : ℕ, ∀ a : A, (ℓ ^ r) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    BrownHypothesesFor Λ X ↔
      ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
        letI := hSums
        ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
          (constantModelBoundedConstructible Λ X K.obj ∧
            DerivedCategory.finiteTorAmplitude _ K.obj) → IsCompactObject K := by
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  apply brownHypothesesFor_iff_compact_of_noetherian ℓ X Λ
  rcases hΛ with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- Integral constructible complexes have finite Tor amplitude, directly from their
finite scalar resolutions and bounded cohomology. This uses no finite-ring examples
or six-functor preservation results. -/
private theorem brownHypotheses_integral_ctf_eq_bc
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X ⊓
      fun K ↦ DerivedCategory.finiteTorAmplitude _ K) =
        constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X := by
  let Λ := Profinite.padicIntegersRingObj ℓ E
  have hmod (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) (hM : IsConstantModelConstructible Λ X M) :
      DerivedCategory.torAmplitudeIn _ (-1) 0
        ((DerivedCategory.singleFunctor _ 0).obj M) := by
    apply torAmplitudeIn_of_constructible_of_uniform_local_model ℓ (Mon.mk Λ)
      (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))) (-1) 0 (by omega) ?_ X M hM
    intro T N hN
    exact padic_constant_local_model_tor ℓ Λ (-1)
      (Or.inl ⟨rfl, Or.inr ⟨E, ⟨Iso.refl _⟩⟩⟩) T N hN
  funext K
  apply propext
  constructor
  · exact And.left
  · intro hK
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1
    have ha' : K.IsGE (min a b) :=
      (DerivedCategory.isGE_iff K _).mpr fun q hq ↦
        (DerivedCategory.isGE_iff K a).mp ha q
          (lt_of_lt_of_le hq (min_le_left _ _))
    refine ⟨hK, min a b - 1, b, ?_⟩
    have ht := torAmplitudeIn_of_cohomology_interval X (Mon.mk Λ) K
      (min a b) b (-1) 0 (min_le_right _ _) (by omega) (fun q hq ↦ ?_)
      (fun q _ ↦ hmod _ (hK.2 q))
    · simpa only [sub_eq_add_neg, add_zero] using ht
    · by_cases hqa : q < min a b
      · exact (DerivedCategory.isGE_iff K _).mp ha' q hqa
      · exact (DerivedCategory.isLE_iff K b).mp hb q (by
          simp only [Set.mem_Icc] at hq
          omega)

open scoped CategoryTheory.Obj in
/-- For integral coefficients, Brown's hypotheses are equivalent to a bound on Ext
from each constructible sheaf, uniform over the second constructible sheaf.
The field may have arbitrary cohomological dimension: the bound is an explicit clause.

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraph 2,
sk-prop-int-compactness-compact, and the finite-support argument in
`WeilConjectures.CategoryTheory.DerivedCategory.NotPreservesCoproducts`.
(blueprint: lem-sfb-brown-integral-ext-criterion).

Proof: integral constructible objects have finite Tor amplitude, so Dctf equals Dbc,
and their localizing closures agree. A Brown bundle makes each constructible sheaf
in degree zero compact. Exact countable products and the disjoint-shift argument
then give a bound uniform over all constructible sheaves in the second argument.
Conversely choose nonnegative bounds from the supplied integer bounds. The integral
compactness theorem makes every bounded constructible object compact in Loc(Dbc).
Transport this assertion across the equality with Loc(Dctf). Thickness and essential
smallness for admissible coefficients, and the formal generation argument, assemble
Brown's bundle. Neither direction uses the disputed arbitrary-field theorem. -/
theorem brownHypothesesFor_padicIntegers_iff_ext_bounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    BrownHypothesesFor (Profinite.padicIntegersRingObj ℓ E) X ↔
      ∀ C : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X,
        ∃ d : ℤ,
          ∀ N : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X,
            ∀ q : ℤ, d < q →
              Subsingleton (((DerivedCategory.singleFunctor _ 0).obj C.obj) ⟶
                ((DerivedCategory.singleFunctor _ 0).obj N.obj)⟦q⟧) := by
  classical
  let Λ := Profinite.padicIntegersRingObj ℓ E
  let B := constantModelBoundedConstructible Λ X
  let S := B ⊓ fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  let L := localizingClosureProEtale Λ X
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  have hcoeff : IsLocalizingAdmissibleCoefficient ℓ Λ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
  have heq : S = B := brownHypotheses_integral_ctf_eq_bc ℓ E X
  have hL : L = localizingClosure B := congrArg localizingClosure heq
  constructor
  · intro hB
    let H : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := IsConstantModelConstructible Λ X
    let _ : H.ContainsZero := constant_heart_zero Λ X
    let _ : H.IsClosedUnderIsomorphisms :=
      (constantModelConstructibleFiniteTor_wellDefined Λ X).1
    have hsingle (C : ConstantModelConstructible Λ X) :
        S ((DerivedCategory.singleFunctor _ 0).obj C.obj) := by
      rw [heq]
      refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
      by_cases hn : n = 0
      · subst n
        exact H.prop_of_iso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app C.obj).symm
          C.property
      · apply H.prop_of_isZero
        rcases lt_or_gt_of_ne hn with hn | hn
        · exact DerivedCategory.isZero_of_isGE _ 0 n hn
        · exact DerivedCategory.isZero_of_isLE _ 0 n hn
    have hmem (C : ConstantModelConstructible Λ X) :
        L ((DerivedCategory.singleFunctor _ 0).obj C.obj) :=
      fun _ _ hSP ↦ hSP _ (hsingle C)
    intro C
    obtain ⟨N, hN⟩ := hB.exists_uniform_hom_single_shift_bound
      ⟨_, hmem C⟩ (hsingle C)
    refine ⟨(N : ℤ), fun M q hq ↦ ?_⟩
    lift q to ℕ using (by omega : 0 ≤ q)
    exact ⟨fun f g ↦ (hN M.obj (hmem M) q (by omega) f).trans
      (hN M.obj (hmem M) q (by omega) g).symm⟩
  · intro hbound
    choose d hd using hbound
    let d' := fun C ↦ (d C).toNat
    have hd' (C N : ConstantModelConstructible Λ X) (q : ℤ)
        (hq : (d' C : ℤ) < q) :
        Subsingleton (((DerivedCategory.singleFunctor _ 0).obj C.obj) ⟶
          ((DerivedCategory.singleFunctor _ 0).obj N.obj)⟦q⟧) :=
      hd C N q ((Int.self_le_toNat (d C)).trans_lt hq)
    have hc := (integralConstructibleCompactness ℓ E k p hp hpℓ X d' hd').2.2
    change ∃ hc : HasCoproducts.{u + 1} (localizingClosure B).FullSubcategory,
      ∀ K : (localizingClosure B).FullSubcategory, B K.obj →
        @IsCompactObject _ _ _ hc K at hc
    rw [← hL] at hc
    obtain ⟨hcop, hc⟩ := hc
    exact (brownHypothesesFor_iff_compact_of_noetherian ℓ X Λ hcoeff).mpr
      ⟨hcop, fun K hK ↦ hc K hK.1⟩


private theorem integer_hom_bound_iff_natural_ext_bound
    {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory.{u + 1} A] [HasExt.{u + 1} A] {I : Type*} (M : I → A) :
    (∀ i, ∃ d : ℤ, ∀ j (q : ℤ), d < q →
      Subsingleton (((DerivedCategory.singleFunctor A 0).obj (M i)) ⟶
        ((DerivedCategory.singleFunctor A 0).obj (M j))⟦q⟧)) ↔
    (∀ i, ∃ d : ℕ, ∀ j (q : ℕ), d ≤ q →
      Subsingleton (Abelian.Ext.{u + 1} (M i) (M j) q)) := by
  constructor
  · intro h i
    obtain ⟨d, hd⟩ := h i
    refine ⟨d.toNat + 1, fun j q hq ↦ ?_⟩
    letI := hd j (q : ℤ) (by omega)
    exact (Abelian.Ext.homEquiv (X := M i) (Y := M j) (n := q)).subsingleton
  · intro h i
    obtain ⟨d, hd⟩ := h i
    refine ⟨(d : ℤ), fun j q hq ↦ ?_⟩
    lift q to ℕ using (by omega : 0 ≤ q)
    letI := hd j q (by omega)
    exact (Abelian.Ext.homEquiv (X := M i) (Y := M j) (n := q)).symm.subsingleton

open scoped CategoryTheory.Obj in
/-- The integral Brown criterion expressed using the categorical Ext groups.
The natural bound may depend on the source constructible sheaf, and is uniform
in the target constructible sheaf. The `HasExt` binder only fixes the size of Ext;
it does not impose a vanishing or compactness hypothesis.

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraph 2,
and sk-prop-int-compactness-compact, with the explicit Ext bound retained.
(blueprint: lem-sfb-brown-integral-categorical-ext-criterion).

Proof: the existing integral criterion identifies Brown's bundle with eventual
vanishing of the ambient Hom groups in integer degrees. Mathlib's canonical
Ext-to-shifted-Hom equivalence transports subsingletonness in both directions.
For an integer bound d use the natural bound d.toNat + 1. Conversely a natural
bound d gives the integer bound d: every integer degree above it is nonnegative
and can be represented by a natural number. Thus negative integer degrees require
no extra assumption, and no bound is inferred merely from the field's characteristic. -/
theorem brownHypothesesFor_padicIntegers_iff_categorical_ext_bounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [HasExt.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))] :
    BrownHypothesesFor (Profinite.padicIntegersRingObj ℓ E) X ↔
      ∀ C : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X,
        ∃ d : ℕ,
          ∀ N : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X,
            ∀ q : ℕ, d ≤ q → Subsingleton (Abelian.Ext.{u + 1} C.obj N.obj q) := by
  exact (brownHypothesesFor_padicIntegers_iff_ext_bounded ℓ E k p hp hpℓ X).trans
    (integer_hom_bound_iff_natural_ext_bound
      (fun C : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X ↦ C.obj))


open scoped CategoryTheory.Obj in
/-- Unbounded categorical Ext from one integral constructible sheaf rules out Brown's bundle.
Only the second sheaf and the degree may vary with the requested lower bound.

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraph 2,
with the explicit Ext bound of sk-prop-int-compactness-compact.
(blueprint: lem-sfb-brown-integral-categorical-ext-criterion).

Proof: the categorical Ext criterion gives a bound d for the fixed source sheaf.
The hypothesis supplies a target sheaf and a degree at least d with a nonzero
Ext class. The bound says that this Ext group is subsingleton, so that class
is zero, a contradiction. This is conditional on genuine unbounded Ext classes;
it asserts no cohomology computation for any particular field. -/
theorem not_brownHypothesesFor_padicIntegers_of_unbounded_categorical_ext
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [HasExt.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))]
    (C : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X)
    (hExt : ∀ d : ℕ,
      ∃ (N : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X)
        (q : ℕ), d ≤ q ∧ ∃ e : Abelian.Ext.{u + 1} C.obj N.obj q, e ≠ 0) :
    ¬ BrownHypothesesFor (Profinite.padicIntegersRingObj ℓ E) X := by
  intro hB
  obtain ⟨d, hd⟩ :=
    (brownHypothesesFor_padicIntegers_iff_categorical_ext_bounded ℓ E k p hp hpℓ X).mp hB C
  obtain ⟨N, q, hq, e, he⟩ := hExt d
  exact he ((hd N q hq).elim e 0)


-- STATEMENT-DISPUTED: The arbitrary-field compactness assertion lacks a finiteness
-- hypothesis on the base field. The finite/rational compactness dependencies require
-- FiniteFieldDatum; the integral one requires an Ext bound. Finite type over an arbitrary
-- positive-characteristic field does not supply finite ℓ-cohomological dimension.
-- Concrete mathematical obstruction: take ell = 2, p = 3, X = Spec k for
-- k = algebraicClosure(F_3)(t_1,t_2,...) and Lambda the constant finite ring F_2.
-- The constant rank-one object is constructible of Tor amplitude [0,0]. Kummer cup
-- symbols in t_1,...,t_n are nonzero in H^n(k,F_2), detected by iterated residues.
-- Exact countable products make the coproduct of its positive shifts also their
-- product. The resulting map with every projection nonzero violates compactness.
-- This is a natural-language counterexample, not a claimed Lean field-cohomology proof.
-- Generation itself is proved without this finiteness assumption by the helpers above.
-- The supplied compactness theorem specifically uses D.k, the algebraic closure of a
-- finite field. Its algebraic-closure coefficient is finite-subextension-valued.
-- The supported geometric finite-field Brown bundle is proved in BrownHypothesesFiniteField;
-- its proof does not assert the original arbitrary-field claim.

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
-- The final compactness input required by this unrestricted statement is unavailable
-- over an arbitrary positive-characteristic field; this remains the original named
-- obligation rather than importing the retired false witness.
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
