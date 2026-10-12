/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.RepresentableLocallyConstant
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

/-- Finite étale morphisms are stable under base change. -/
instance isStableUnderBaseChange_isFinite_inf_etale :
    (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange :=
  MorphismProperty.IsStableUnderBaseChange.inf

/-- A sheaf of sets `E` on the small étale site of `T` is *finite locally constant* if there
is an étale cover of `T` (`AlgebraicGeometry.Scheme.etalePrecoverage`) such that the
restriction of `E` to each member of the cover is constant, and the stalks of `E` at all
geometric points are finite. This is the analogue for sheaves of sets of
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf`, which is stated for abelian
coefficients. -/
def Scheme.IsFiniteLocallyConstantSheafOfTypes {T : Scheme.{u}}
    (E : Sheaf T.smallEtaleTopology (Type (u + 1))) : Prop :=
  (∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage T, ∀ i,
    (E.over (𝒰.etalePrecoverageToEtale i)).IsConstant
      (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))) ∧ Scheme.IsFiniteSheaf E

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
        Nonempty (E.obj ≅ uliftYoneda.{u + 1}.obj (Scheme.Etale.mk π)) := by
  refine ⟨fun P π _ _ ↦ ?_, fun E hE ↦ ?_⟩
  · let X : T.Etale := Scheme.Etale.mk π
    have : IsFinite X.hom := ‹IsFinite π›
    refine ⟨(T.smallEtaleTopology.uliftYoneda.{u + 1}.obj X).property, ?_, ?_⟩
    · choose U g hg S hS fst hy hpb using
        fun y ↦ FiniteEtale.exists_etale_isPullback_sigma ⟨X, this⟩ y
      let 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage T :=
        Scheme.Cover.mkOfCovers T U g (fun y ↦ ⟨y, hy y⟩) hg
      exact ⟨𝒰, fun y ↦ Etale.isConstant_over_uliftYoneda_of_isPullback (hpb y)⟩
    · exact ⟨fun Ω _ _ s ↦ (ConcreteCategory.isFinitelyGenerated_iff_finite _).2
        (Etale.finite_sheafFiber_uliftYoneda X s)⟩
  · obtain ⟨𝒰, h𝒰⟩ := hE.1
    obtain ⟨X, hX, ⟨r⟩⟩ := Etale.exists_representableBy_of_isConstant E 𝒰 h𝒰 hE.2
    exact ⟨X.left, X.hom, hX, X.prop,
      ⟨((Functor.RepresentableBy.equivUliftYonedaIso _ _) r).symm⟩⟩

section Henselian

variable {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
  {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] (i : Y₀ ⟶ Y)
  (f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))

/-- **Idempotent lifting for the structure sheaf over a henselian pair.** Let `(A, I)` be a
henselian pair, `f : Y ⟶ Spec A` proper and `i : Y₀ ⟶ Y` the closed fibre over `Spec A/I`.
Then restriction `Γ(Y, 𝒪_Y) ⟶ Γ(Y₀, 𝒪_{Y₀})` induces a bijection between the idempotents
of the two rings; equivalently the open and closed subschemes of `Y₀` are exactly the closed
fibres of those of `Y`. The restriction map itself need not be bijective.
(blueprint: `thm-weil-pbc-henselian-idempotent-lifting`) -/
@[stacks 0A0B]
theorem Scheme.bijective_appTop_idempotent_of_henselianRing
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    Function.Bijective (fun e : {e : Γ(Y, ⊤) // IsIdempotentElem e} ↦
      (⟨i.appTop.hom e.1, e.2.map i.appTop.hom⟩ : {e : Γ(Y₀, ⊤) // IsIdempotentElem e})) :=
  sorry

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
  sorry

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
  sorry

end AlgebraicGeometry
