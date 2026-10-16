/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets
public import WeilConjectures.AlgebraicGeometry.HenselianClosedFiberNonempty

import Sheaf.AlgebraicGeometry.HenselianClopenRestriction
import WeilConjectures.AlgebraicGeometry.SchemeClopenIdempotent
import Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful
import Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity
import Sheaf.AlgebraicGeometry.FiniteEtaleYonedaLocalTrivializations
import Sheaf.AlgebraicGeometry.FiniteLocallyConstantSetsRepresentability
import Sheaf.AlgebraicGeometry.FiniteEtaleEquivalenceH1

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.RingTheory.LocalRing.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Finite étale schemes over a proper scheme over a henselian pair

Let `(A, I)` be a henselian pair, `f : Y ⟶ Spec A` a proper morphism and
`Y₀ = Y ×_A A/I` its closed fibre, with closed immersion `i : Y₀ ⟶ Y`. The closed fibre
controls the "discrete" invariants of `Y`:

* the idempotents of `Γ(Y, 𝒪_Y)` and of `Γ(Y₀, 𝒪_{Y₀})` correspond under restriction, i.e.
  the open and closed subschemes of `Y` and `Y₀` correspond;
* base change along `i` is an equivalence between the categories of finite étale schemes
  over `Y` and over `Y₀`;
* restriction is a bijection `H¹(Y, M) ≃ H¹(Y₀, M)` for every finite abelian group `M`.

The last statement goes through the dictionary between finite locally constant sheaves of
sets on the small étale site of a scheme and finite étale schemes over it, which is also
recorded here.

The category of finite étale `Y`-schemes is `(@IsFinite ⊓ @Etale).Over ⊤ Y`, and base
change along `i` is `CategoryTheory.MorphismProperty.Over.pullback`. The closed fibre is
given by a cartesian square
```
Y₀ ---i---> Y
|           |
f₀          f
v           v
Spec A/I --> Spec A
```

## Main statements

- `AlgebraicGeometry.Scheme.bijective_appTop_idempotent_of_henselianRing`: idempotent lifting
  for the structure sheaf of a proper scheme over a henselian pair.
- `AlgebraicGeometry.Scheme.injective_appTop_idempotent_of_le_jacobson`: the uniqueness half of
  the idempotent lifting, valid whenever `I` lies in the Jacobson radical.
- `AlgebraicGeometry.Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing`:
  finite étale lifting over a proper scheme over a henselian pair.
- `AlgebraicGeometry.Scheme.isEquivalence_pullback_finiteEtale_of_henselianLocalRing`:
  the same over a henselian local ring and its residue field.
- `AlgebraicGeometry.Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso`: the sheaf of
  sections of a finite étale scheme is finite locally constant, and every finite locally
  constant sheaf of sets is of this form.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_one_constantSheaf_of_henselianRing`:
  the `H¹` comparison for a finite constant sheaf.

## References

- Stacks Project, Section 59.91, <https://stacks.math.columbia.edu/tag/0A3S>
- Stacks Project, Étale Cohomology, Section "Locally constant sheaves" (finite locally
  constant sheaves of sets and finite étale schemes)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ### Auxiliary lemmas -/

/-- The basic open `D(e)` of an idempotent global section `e` is closed: its complement is
the basic open `D(1 - e)` of the complementary idempotent. -/
lemma Scheme.isClosed_basicOpen_of_isIdempotentElem {X : Scheme.{u}} {e : Γ(X, ⊤)}
    (he : IsIdempotentElem e) : IsClosed (X.basicOpen e : Set X) := by
  have hcompl : (X.basicOpen e : Set X)ᶜ = X.basicOpen (1 - e) := by
    ext x
    have hx := IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
      (he.map (X.presheaf.germ ⊤ x trivial).hom)
    simp only [Set.mem_compl_iff, SetLike.mem_coe, Scheme.mem_basicOpen_top, map_sub, map_one]
    rcases hx with h | h <;> simp [h]
  rw [← isOpen_compl_iff, hcompl]
  exact (X.basicOpen (1 - e)).isOpen

/-- An idempotent global section `e` whose basic open `D(e)` is empty is zero: each germ of `e`
is an idempotent of a local ring, hence `0` or `1`, and it is not `1` since `D(e) = ∅`. -/
lemma Scheme.eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot {X : Scheme.{u}} {e : Γ(X, ⊤)}
    (he : IsIdempotentElem e) (h : X.basicOpen e = ⊥) : e = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ e 0 fun x _ ↦ ?_
  rcases IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
      (he.map (X.presheaf.germ ⊤ x trivial).hom) with h' | h'
  · rw [map_zero]
    exact h'
  · have hx : x ∈ X.basicOpen e := by
      rw [Scheme.mem_basicOpen_top]
      change IsUnit ((X.presheaf.germ ⊤ x trivial).hom e)
      rw [h']
      exact isUnit_one
    rw [h] at hx
    exact absurd hx (by simp)

/-- **Uniqueness of idempotent lifts to a proper scheme.** Let `I ⊆ A` be an ideal contained in
the Jacobson radical (e.g. `(A, I)` a henselian pair), `f : Y ⟶ Spec A` proper and
`i : Y₀ ⟶ Y` the closed fibre over `Spec A/I`. Then restriction along `i` is injective on
idempotent global sections. If `e₁, e₂` are idempotents with the same restriction, then the
idempotent `d = e₁ + e₂ - 2 e₁ e₂` restricts to `0`, so the clopen `D(d)` misses `Y₀`; since
every nonempty closed subset of `Y` meets `Y₀`, `D(d) = ∅`, hence `d = 0` and `e₁ = e₂`.
This is the injectivity half of
`AlgebraicGeometry.Scheme.bijective_appTop_idempotent_of_henselianRing`. -/
theorem Scheme.injective_appTop_idempotent_of_le_jacobson {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥) {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A))
    [IsProper f] (i : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    Function.Injective (fun e : {e : Γ(Y, ⊤) // IsIdempotentElem e} ↦
      (⟨i.appTop.hom e.1, e.2.map i.appTop.hom⟩ : {e : Γ(Y₀, ⊤) // IsIdempotentElem e})) := by
  rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ heq
  have heq' : i.appTop.hom e₁ = i.appTop.hom e₂ := congrArg Subtype.val heq
  have h₁' : e₁ * e₁ = e₁ := h₁
  have h₂' : e₂ * e₂ = e₂ := h₂
  set d : Γ(Y, ⊤) := e₁ + e₂ - 2 * e₁ * e₂ with hd_def
  have hd : IsIdempotentElem d := by
    change d * d = d
    rw [hd_def]
    linear_combination (1 - 4 * e₂ + 4 * e₂ ^ 2) * h₁' + h₂'
  have hid : i.appTop.hom d = 0 := by
    have h₂'' : i.appTop.hom e₂ * i.appTop.hom e₂ = i.appTop.hom e₂ := h₂.map i.appTop.hom
    rw [hd_def, map_sub, map_add, map_mul, map_mul, map_ofNat, heq']
    linear_combination (-2) * h₂''
  -- The closed fibre is the preimage of `V(I)`.
  have hrange : Set.range i = f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
    have hq := range_comap_of_surjective (A ⧸ I) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker] at hq
    rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.2 h.isoPullback.hom.surjective, Set.image_univ,
      Scheme.Pullback.range_fst]
    exact congrArg (f ⁻¹' ·) hq
  have hbot : Y.basicOpen d = ⊥ := by
    by_contra hne
    obtain ⟨y, hy, hy₀⟩ := f.nonempty_inter_preimage_zeroLocus I hI
      (isClosed_basicOpen_of_isIdempotentElem hd)
      (not_not.mp (mt (TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp hne))
    rw [← hrange] at hy₀
    obtain ⟨y₀, rfl⟩ := hy₀
    have hmem : y₀ ∈ i ⁻¹ᵁ Y.basicOpen d := hy
    rw [Scheme.preimage_basicOpen_top] at hmem
    change y₀ ∈ Y₀.basicOpen (i.appTop.hom d) at hmem
    rw [hid, Scheme.basicOpen_zero] at hmem
    exact absurd hmem (by simp)
  have hd0 : d = 0 := eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot hd hbot
  rw [hd_def] at hd0
  refine Subtype.ext ?_
  change e₁ = e₂
  linear_combination (e₁ - e₂) * hd0 - (1 - 2 * e₂) * h₁' + (1 - 2 * e₁) * h₂'

/-! ### Finite locally constant sheaves and finite étale schemes -/

/-- **Finite locally constant sheaves of sets are finite étale schemes.** For a scheme `T`:

* for every finite étale `π : P ⟶ T`, the presheaf of sections `U ↦ Hom_T(U, P)` on the small
  étale site (the Yoneda presheaf of `P`, viewed as an étale `T`-scheme) is a sheaf, and it
  is finite locally constant;
* every finite locally constant sheaf of sets `E` is isomorphic to the sheaf of sections of
  a finite étale `T`-scheme.

These are the two object-level halves of the blueprint node. Together with the Yoneda lemma
(morphisms of the sheaves of sections are `T`-morphisms) they give the equivalence between
finite étale `T`-schemes and finite locally constant sheaves of sets, and with it the
statement about finite group actions; neither is stated here.
(blueprint: `lemma-weil-pbc-finite-locally-constant-etale-equivalence`) -/
theorem Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso (T : Scheme.{u}) :
    (∀ (P : Scheme.{u}) (π : P ⟶ T) [IsFinite π] [Etale π],
      ∃ h : Presheaf.IsSheaf T.smallEtaleTopology (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk π)),
        IsFiniteLocallyConstantSheafOfTypes ⟨_, h⟩) ∧
    ∀ E : Sheaf T.smallEtaleTopology (Type (u + 1)), IsFiniteLocallyConstantSheafOfTypes E →
      ∃ (P : Scheme.{u}) (π : P ⟶ T) (_ : IsFinite π) (_ : Etale π),
        Nonempty (E.obj ≅ uliftYoneda.{u + 1}.obj (Scheme.Etale.mk π)) :=
  by
    constructor
    · intro P π _ _
      let F := (T.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Scheme.Etale.mk π)
      obtain ⟨⟨𝒰, h𝒰⟩, hfin⟩ := Scheme.finiteEtale_yoneda_local_trivializations T P π
      refine ⟨F.property, ⟨⟨𝒰, ?_⟩, hfin⟩⟩
      intro j
      obtain ⟨S, _, ⟨e⟩⟩ := h𝒰 j
      exact Sheaf.isConstant_of_iso _ e
    · intro E hE
      exact Scheme.finiteLocallyConstant_sets_representable T E hE.1 hE.2


section Henselian

variable {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
  {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] (i : Y₀ ⟶ Y)
  (f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))

/-- **Idempotent lifting for the structure sheaf over a henselian pair.** Let `(A, I)` be a
henselian pair, `f : Y ⟶ Spec A` proper and `i : Y₀ ⟶ Y` the closed fibre over `Spec A/I`.
Then restriction `Γ(Y, 𝒪_Y) ⟶ Γ(Y₀, 𝒪_{Y₀})` induces a bijection between the idempotents
of the two rings; equivalently the open and closed subschemes of `Y₀` are exactly the closed
fibres of those of `Y`. The restriction map itself need not be bijective.
Injectivity is `AlgebraicGeometry.Scheme.injective_appTop_idempotent_of_le_jacobson`.
(blueprint: `thm-weil-pbc-henselian-idempotent-lifting`) -/
@[stacks 0A0B]
theorem Scheme.bijective_appTop_idempotent_of_henselianRing
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    Function.Bijective (fun e : {e : Γ(Y, ⊤) // IsIdempotentElem e} ↦
      (⟨i.appTop.hom e.1, e.2.map i.appTop.hom⟩ : {e : Γ(Y₀, ⊤) // IsIdempotentElem e})) :=
  by
    obtain ⟨hinj, hsurj⟩ := Scheme.henselian_clopen_restriction I f i f₀ h
    have hY := scheme_clopen_idempotent Y
    have hY₀ := scheme_clopen_idempotent Y₀
    constructor
    · intro e e' he
      apply hY.2.1.1
      apply hinj _ _
      · exact ⟨(hY.1 e.1 e.2).2.1, (hY.1 e.1 e.2).2.2.1⟩
      · exact ⟨(hY.1 e'.1 e'.2).2.1, (hY.1 e'.1 e'.2).2.2.1⟩
      · rw [← (hY.2.2.2 i e.1 e.2).2, ← (hY.2.2.2 i e'.1 e'.2).2]
        exact congrArg (fun x ↦ idempotentOpen x.1) he
    · intro e₀
      obtain ⟨U, hU, hres⟩ := hsurj (idempotentOpen e₀.1)
        ⟨(hY₀.1 e₀.1 e₀.2).2.1, (hY₀.1 e₀.1 e₀.2).2.2.1⟩
      obtain ⟨e, he, hloc⟩ := hY.2.1.2 U hU
      refine ⟨⟨e, he⟩, hY₀.2.1.1 ?_⟩
      change idempotentOpen (i.appTop e) = idempotentOpen e₀.1
      rw [(hY.2.2.2 i e he).2, hloc, hres]

/-- **Finite étale lifting over a proper scheme over a henselian pair.** Let `(A, I)` be a
henselian pair, `f : Y ⟶ Spec A` proper and `i : Y₀ ⟶ Y` the closed fibre over `Spec A/I`.
Then base change along `i` is an equivalence from the category of finite étale `Y`-schemes
to the category of finite étale `Y₀`-schemes. In particular morphisms, and hence finite
group actions (finitely many automorphisms subject to finitely many equations), lift
uniquely.
(blueprint: `thm-weil-pbc-finite-etale-lifting`) -/
@[stacks 0A48]
theorem Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence :=
  by
    obtain ⟨hff⟩ := Scheme.fullyFaithful_pullback_finiteEtale_of_henselianRing
      inferInstance I f i f₀ h
    have := hff.full
    have := hff.faithful
    let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    let k := pullback.fst f j
    let e := h.isoPullback
    have hess : (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).EssSurj := by
      constructor
      intro V
      have : IsFinite V.hom := V.prop.1
      have : Etale V.hom := V.prop.2
      let V' : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
          (pullback f j) := MorphismProperty.Over.mk ⊤ (V.hom ≫ e.hom)
            ⟨inferInstance, inferInstance⟩
      obtain ⟨U, ⟨a⟩⟩ := Scheme.essSurj_pullback_finiteEtale_of_henselianRing I f V'
      let q := asIso (pullback.map U.hom i U.hom k
        (𝟙 _) e.hom (𝟙 _) (by simp) (by simp [k, j, e]))
      refine ⟨U, ⟨MorphismProperty.Over.isoMk (q ≪≫ (CategoryTheory.Over.forget _).mapIso a) ?_⟩⟩
      change q.hom ≫ a.hom.left ≫ V.hom = pullback.snd U.hom i
      apply (cancel_mono e.hom).1
      have ha : a.hom.left ≫ V.hom ≫ e.hom = pullback.snd U.hom k := a.hom.w
      simp only [Category.assoc, ha]
      dsimp [q]
      simp
    exact ⟨inferInstance, inferInstance, hess⟩

end Henselian

/-- **Finite étale lifting over a henselian local ring.** Let `A` be a henselian local ring,
`f : Y ⟶ Spec A` proper and `i : Y₀ ⟶ Y` the closed fibre over the residue field. Then base
change along `i` is an equivalence from the category of finite étale `Y`-schemes to the
category of finite étale `Y₀`-schemes; in particular morphisms and finite group actions
lift uniquely. This is the case `I = 𝔪` of
`AlgebraicGeometry.Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing`.
(blueprint: `lemma-weil-pbc-finite-etale-henselian-lifting`) -/
theorem Scheme.isEquivalence_pullback_finiteEtale_of_henselianLocalRing
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] (i : Y₀ ⟶ Y)
    (f₀ : Y₀ ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) :
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence :=
  Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing (IsLocalRing.maximalIdeal A) f i
    f₀ h

/-- **The `H¹` comparison for a finite constant sheaf over a henselian pair.** Let `(A, I)` be
a henselian pair, `f : Y ⟶ Spec A` proper and `i : Y₀ ⟶ Y` the closed fibre over `Spec A/I`.
For every finite abelian group `M`, restriction `H¹(Y, M) ⟶ H¹(Y₀, M)` along `i` is
bijective. Both sides classify `M`-torsors, i.e. finite étale schemes with a simply
transitive `M`-action (`AlgebraicGeometry.Scheme.EtaleTorsor.exists_quotientEquivSheafH`),
and these correspond under the finite étale lifting
`AlgebraicGeometry.Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing`.
(blueprint: `lemma-weil-pbc-h1-torsor-comparison`) -/
theorem Etale.bijective_cohomologyMap_one_constantSheaf_of_henselianRing
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] (i : Y₀ ⟶ Y)
    (f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (M : Type (u + 1)) [AddCommGroup M] [Finite M] :
    Function.Bijective (Etale.cohomologyMap i
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)) 1) :=
  by
    have hFE := Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing I f i f₀ h
    exact Etale.bijective_cohomologyMap_one_of_finiteEtale_equivalence i hFE M

end AlgebraicGeometry
