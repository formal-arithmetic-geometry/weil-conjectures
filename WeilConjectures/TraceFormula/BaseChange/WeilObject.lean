/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobenius
public import WeilConjectures.TraceFormula.BaseChange.Basic
public import WeilConjectures.TraceFormula.Stalk
public import WeilConjectures.TraceFormula.BaseChange.Coherence

/-!

# The base change of Weil objects from a finite field to an algebraically closed field

Let `ℓ` be a prime, `k = 𝔽_q` a finite field of characteristic `p ≠ ℓ`, `Ω` a separably closed
field containing `k` (in the applications the algebraic closure `k̄`), `X` a separated scheme of
finite type over `Spec k` and `π : X̄ = X ×_k Ω ⟶ X` its base change
(`WeilConjectures.TraceFormula.BaseChange.Basic`). A Weil object `(K, φ)` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for
an endomorphism `g` of `X` over `Spec k` gives a Weil object `(Lπ^* K, φ̄)` of `Dᵇc(X̄)⟦ℚ̲̄_ℓ⟧`
for the model Frobenius `Φ = (g ≫ F_X^N) ×_k Ω` (`baseChangeModelFrobenius`), with
`N = n + 1` (`ProEtale.CondensedRing.weilGeometricBaseChange`). Its structure isomorphism is
```
LΦ^* Lπ^* K ≅ L(Φ ≫ π)^* K = L(π ≫ g ≫ F_X^N)^* K ≅ Lπ^* Lg^* LF_X^{N*} K
  --Lκ--> Lπ^* Lg^* K --Lπ^* φ--> Lπ^* K,
```
where `κ : (F_X^N)^* ≅ 𝟭` is the trivialization of the pullback along the `q^N`-power Frobenius
(`ProEtale.CondensedRing.upperStarFrobeniusIso`). For an automorphism `e` of `X` and
`g = e^{n+1}`, this is the bridge between the Weil objects of
`WeilConjectures.TraceFormula.Statement`, over `k` with the Frobenius `σ^{n+1}` twisted by
`e^{n+1}`, and the model-Frobenius setting of the Lefschetz–Verdier formula over `k̄`.

## The Frobenius trivialization

The absolute Frobenius of a scheme of characteristic `p` acts trivially on its pro-étale topos:
the relative Frobenius of a weakly étale `V ⟶ X` is an isomorphism, so the base change along the
absolute Frobenius is isomorphic to the identity on the pro-étale site (blueprint
`lem-trf-absolute-frobenius-site`, `ProEtale.upperStarIterateFrobeniusIso`). Writing
`#k = p ^ a`, the Frobenius `F_X^N` is the absolute `p ^ (a N)`-power Frobenius. Its
trivialization on abelian sheaves is monoidal and fixes the coefficient ring `Λ_X`, which is
pulled back from the point, so it gives `κ : (F_X^N)^* ≅ 𝟭` on `ℚ̲̄_ℓ`-modules
(`ProEtale.CondensedRing.upperStarFrobeniusIso`). At a
geometric point `ȳ : Spec Ω ⟶ X`, the trivialization `κ` restricts to the trivialization
`(σ)^* ≅ 𝟭` of the pullback along the automorphism `σ` of `Spec Ω` inverse to the
`q^N`-power Frobenius of `Spec Ω` (`upperStarIsoIdOfIsSepClosed`), since `(σ ≫ ȳ) ≫ F_X^N = ȳ`
(`ProEtale.CondensedRing.isGaloisCompatibleFrobeniusIso_upperStarFrobeniusIso`).

## Main definitions

- `ProEtale.CondensedRing.upperStarFrobeniusIso`: the trivialization `(F_X^N)^* ≅ 𝟭`, and its
  derived version `ProEtale.CondensedRing.leftDerivedUpperStarFrobeniusIso`.
- `ProEtale.CondensedRing.geometricBaseChangeUpperStar`: the derived pullback
  `Lπ^* : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X̄)⟦ℚ̲̄_ℓ⟧` along the base change.
- `ProEtale.CondensedRing.weilGeometricBaseChange`: the base change of Weil objects
  `WeilBoundedConstructible ℓ g ⥤ WeilBoundedConstructible ℓ (baseChangeModelFrobenius Ω X (n + 1)
      g)`.

## Sorried inputs

- `ProEtale.CondensedRing.isGaloisCompatibleFrobeniusIso_upperStarFrobeniusIso`: the Galois
  compatibility of the Frobenius trivialization at geometric points (unfinished).
- `ProEtale.CondensedRing.boundedConstructible_leftDerivedUpperStar_geometricBaseChangeProj_obj`:
  the pullback along `π` preserves bounded constructible complexes (blueprint
  `sk-thm-sf-ctf-stability`, section `sec-six-functors-basics`, with the pullback of
  constructible sheaves `prop-constructible-pullback`).

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Iso

variable {C E : Type*} [Category C] [Category E] {A C' : C ⥤ E} {B : C ⥤ C}

/-- The isomorphism `A ≅ C'` obtained from `A ≅ B ⋙ C'` and a trivialization `B ≅ 𝟭`. -/
def compIsoOfIsoId (c : A ≅ B ⋙ C') (κ : B ≅ 𝟭 C) : A ≅ C' :=
  c ≪≫ Functor.isoWhiskerRight κ C' ≪≫ C'.leftUnitor

/-- The components of `compIsoOfIsoId c κ` are the composites
```
A M --c--> C' (B M) --C' κ_M--> C' M.
```
-/
lemma compIsoOfIsoId_hom_app (c : A ≅ B ⋙ C') (κ : B ≅ 𝟭 C) (M : C) :
    (compIsoOfIsoId c κ).hom.app M = c.hom.app M ≫ C'.map (κ.hom.app M) := by
  simp [compIsoOfIsoId]

end CategoryTheory.Iso

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] [Finite k] {Ω : Type u} [Field Ω] [Algebra k Ω]

omit [Algebra k Ω] in
/-- Let `σ` be an automorphism of `Spec Ω` whose inverse is `Spec(y ↦ y ^ (#k ^ N))`. A morphism
`ȳ : Spec Ω ⟶ X` satisfies `(σ ≫ ȳ) ≫ F_X^N = ȳ`: the `#k ^ N`-power Frobenius `F_X^N` acts on
`σ ≫ ȳ` through the `#k ^ N`-power map of `Ω`. -/
lemma comp_comp_frobeniusIterate_overFrobenius_left [Algebra k Ω] {X : Over (Spec (.of k))}
    {N : ℕ} {σ : Spec (.of Ω) ≅ Spec (.of Ω)} (hσ : σ.inv = Spec.map (powCardPowRingHom k Ω N))
    (y : Spec (.of Ω) ⟶ X.left) :
    (σ.hom ≫ y) ≫ (frobeniusIterate (overFrobenius X) N).left = y := by
  rw [isFrobenius_frobeniusIterate_overFrobenius_left X N _ _ (powCardPowRingHom_apply N), ← hσ,
    Iso.inv_hom_id_assoc]

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The Frobenius trivialization -/

section Frobenius

variable (X : Over (Spec (.of k))) (N : ℕ)

/-- The compatibility at a geometric point `ȳ : Spec Ω ⟶ X` of a trivialization `κ : F^* ≅ 𝟭` of
the pullback along the `#k ^ N`-power Frobenius `F` with a trivialization `τ : σ^* ≅ 𝟭` of the
pullback along the automorphism `σ` of `Spec Ω` inverse to the `#k ^ N`-power Frobenius: writing
`ȳ = (σ ≫ ȳ) ≫ F`, the two identifications `ȳ^* M ≅ σ^* ȳ^* M ≅ (σ ≫ ȳ)^* M` and
`ȳ^* M = ((σ ≫ ȳ) ≫ F)^* M ≅ (σ ≫ ȳ)^* F^* M --κ--> (σ ≫ ȳ)^* M` agree. -/
def IsGaloisCompatibleFrobeniusIsoAt
    (κ : ((frobeniusIterate (overFrobenius X) N).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _)
    {Ω : Type u} [Field Ω] [Algebra k Ω] (σ : Spec (.of Ω) ≅ Spec (.of Ω))
    (hσ : σ.inv = Spec.map (powCardPowRingHom k Ω N)) (y : Spec (.of Ω) ⟶ X.left)
    (τ : (σ.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _) : Prop :=
  ∀ M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left),
    τ.inv.app ((y)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ.hom y).inv.app M =
      eqToHom (congrArg (fun t : Spec (.of Ω) ⟶ X.left ↦
          (t)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M)
          (comp_comp_frobeniusIterate_overFrobenius_left hσ y).symm) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) (σ.hom ≫ y)
          (frobeniusIterate (overFrobenius X) N).left).hom.app M ≫
        (σ.hom ≫ y)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map (κ.hom.app M)

/-- **Galois compatibility of a trivialization of the Frobenius pullback** (blueprint
`lem-trf-absolute-frobenius-site`, with its comparison with the Galois pullbacks at geometric
points, blueprint `prop-trf-scheme-galois-comparison`). Let `X` be a scheme over the finite field
`k` and `F = F_X^N` its `#k ^ N`-power Frobenius. The pullback `F^*` on `ℚ̲̄_ℓ`-modules on the
pro-étale site of `X` has a trivialization `κ : F^* ≅ 𝟭`: the relative Frobenius of a weakly
étale `V ⟶ X` is a weakly étale universal homeomorphism, hence an isomorphism, so the base
change along `F` is isomorphic to the identity on the pro-étale site.

At a geometric point the canonical trivialization is the trivialization of a Galois pullback:
let `Ω ⊇ k` be separably closed, `σ` the automorphism of `Spec Ω` inverse to the
`#k ^ N`-power Frobenius `F_Ω = Spec(y ↦ y ^ (#k ^ N))` (for `Ω = k̄`, the `N`-th power of the
Galois Frobenius) and `ȳ : Spec Ω ⟶ X`. Writing `ȳ = (σ ≫ ȳ) ≫ F`
(`comp_comp_frobeniusIterate_overFrobenius_left`), the two identifications
```
ȳ^* M ≅ σ^* ȳ^* M ≅ (σ ≫ ȳ)^* M,
ȳ^* M = ((σ ≫ ȳ) ≫ F)^* M ≅ (σ ≫ ȳ)^* F^* M --κ--> (σ ≫ ȳ)^* M
```
agree, the first one through the trivialization `τ : σ^* ≅ 𝟭` of `upperStarIsoIdOfIsSepClosed`.
Indeed `κ` is compatible with pullbacks along morphisms of schemes of characteristic `p`, and on
`Spec Ω` the trivialization `κ` of `F_Ω^*` is the inverse of `τ` composed with the identity
`(F_Ω ≫ σ)^* = 𝟙^*`: both are the identity on the sheaves pulled back from the condensed point,
which are all sheaves on `Spec Ω`. -/
def IsGaloisCompatibleFrobeniusIso
    (κ : ((frobeniusIterate (overFrobenius X) N).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _) :
    Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra k Ω] (σ : Spec (.of Ω) ≅ Spec (.of Ω))
    (hσ : σ.inv = Spec.map (powCardPowRingHom k Ω N)) (y : Spec (.of Ω) ⟶ X.left),
    IsGaloisCompatibleFrobeniusIsoAt ℓ X N κ σ hσ y
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom)

/-- **The trivialization of the Frobenius pullback** (blueprint `lem-trf-absolute-frobenius-site`):
the pullback along the `#k ^ N`-power Frobenius `F = F_X^N` on `ℚ̲̄_ℓ`-modules on the pro-étale
site of `X` is trivialized by the relative Frobenius isomorphisms. Writing `#k = p ^ a`, the
Frobenius `F` is the absolute `p ^ (a N)`-power Frobenius (`frobeniusIterate_overFrobenius_left`),
whose pullback of abelian sheaves has the monoidal trivialization
`ProEtale.upperStarIterateFrobeniusIso`; it fixes the coefficient ring `Λ_X`, which is pulled back
from the point (`ProEtale.upperStarIterateFrobeniusIso_hom_app_upperStarFromPoint`), so it
induces a trivialization on `Λ_X`-modules (`upperStarIterateFrobeniusIso`). -/
noncomputable def upperStarFrobeniusIso :
    ((frobeniusIterate (overFrobenius X) N).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _ :=
  upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) (frobeniusIterate_overFrobenius_left X N) ≪≫
    upperStarIterateFrobeniusIso (Profinite.padicAlgClRingObj ℓ) (FiniteField.ringChar_prime k)
      (isOfCharacteristic_of_hom_spec X.hom) (FiniteField.frobeniusExponent k * N)

/-- At geometric points, the trivialization of the Frobenius pullback is the trivialization of
the Galois pullback (`IsGaloisCompatibleFrobeniusIso`). -/
theorem isGaloisCompatibleFrobeniusIso_upperStarFrobeniusIso :
    IsGaloisCompatibleFrobeniusIso ℓ X N (upperStarFrobeniusIso ℓ X N) :=
  sorry

/-- The trivialization `Lκ : L(F_X^N)^* ≅ 𝟭` of the derived pullback along the `#k ^ N`-power
Frobenius: the derived functor of `upperStarFrobeniusIso`. -/
noncomputable def leftDerivedUpperStarFrobeniusIso :
    L(((frobeniusIterate (overFrobenius X) N).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ≅ 𝟭 _ :=
  Functor.leftDerivedFunctorIdIso (upperStarFrobeniusIso ℓ X N)

end Frobenius

/-! ### The pullback along the base change -/

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

section UpperStar

/-- The derived pullback along the base change `π : X̄ ⟶ X` preserves bounded constructible
complexes (blueprint `sk-thm-sf-ctf-stability`, with the pullback of constructible sheaves
`prop-constructible-pullback`): `Lπ^*` is computed levelwise by the exact functor `π^*`, so it
commutes with the homology sheaves, and the pullback of a sheaf which is constructible along a
finite stratification of `X` by locally closed constructible strata is constructible along the
preimage stratification of `X̄`, the projection `π` being affine. -/
theorem boundedConstructible_leftDerivedUpperStar_geometricBaseChangeProj_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) K) :
    boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) ((geometricBaseChange k Ω).obj X).left)
      ((L((geometricBaseChangeProj (Ω := Ω) X)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K) :=
  sorry

variable (Ω) in
/-- The derived pullback `Lπ^* : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X̄)⟦ℚ̲̄_ℓ⟧` along the base change
`π : X̄ ⟶ X`: the restriction of `L((π)^*⟦ℚ̲̄_ℓ⟧)`. -/
noncomputable def geometricBaseChangeUpperStar :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(((geometricBaseChange k Ω).obj X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
      L((geometricBaseChangeProj X)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_geometricBaseChangeProj_obj ℓ X K.obj
      K.property

@[simp]
lemma geometricBaseChangeUpperStar_obj_obj (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((geometricBaseChangeUpperStar Ω ℓ X).obj K).obj =
      L((geometricBaseChangeProj X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj :=
  rfl

@[simp]
lemma geometricBaseChangeUpperStar_map_hom {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : K ⟶ K') :
    ((geometricBaseChangeUpperStar Ω ℓ X).map φ).hom =
      L((geometricBaseChangeProj X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map φ.hom :=
  rfl

end UpperStar

/-! ### The base change of Weil objects -/

section Weil

variable (N : ℕ) (g : X ⟶ X)

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The model Frobenius `Φ = (g ≫ F_X^N) ×_k Ω` lies over `g ≫ F_X^N`. -/
lemma modelFrobenius_left_comp_proj' :
    (baseChangeModelFrobenius Ω X N g).left ≫ geometricBaseChangeProj X =
      geometricBaseChangeProj X ≫ g.left ≫ (frobeniusIterate (overFrobenius X) N).left :=
  modelFrobenius_left_comp_proj X N g

variable (Ω) in
/-- The Frobenius comparison of the base change on the ambient derived categories:
`L(Φ ≫ π)^* ≅ Lπ^* Lg^*`, the composite
```
L(Φ ≫ π)^* = L(π ≫ g ≫ F)^* ≅ Lπ^* L(g ≫ F)^* ≅ Lπ^* Lg^* LF^* --Lκ--> Lπ^* Lg^*
```
for `F = F_X^N`. -/
noncomputable def leftDerivedUpperStarModelFrobeniusIso :
    L(((baseChangeModelFrobenius Ω X N g).left ≫ geometricBaseChangeProj X)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧) ≅
      L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L((geometricBaseChangeProj X)^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  pullbackCongrIso (D := fun S ↦ DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) S)))
      (fun t ↦ L((t)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
      (modelFrobenius_left_comp_proj' X N g) ≪≫
    leftDerivedUpperStarComp _ (geometricBaseChangeProj X)
      (g.left ≫ (frobeniusIterate (overFrobenius X) N).left) ≪≫
    Functor.isoWhiskerRight (Iso.compIsoOfIsoId
      (leftDerivedUpperStarComp _ g.left (frobeniusIterate (overFrobenius X) N).left)
      (leftDerivedUpperStarFrobeniusIso ℓ X N)) _

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The components of `leftDerivedUpperStarModelFrobeniusIso`. -/
lemma leftDerivedUpperStarModelFrobeniusIso_hom_app
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))) :
    (leftDerivedUpperStarModelFrobeniusIso Ω ℓ X N g).hom.app M =
      eqToHom (congrArg (fun t : ((geometricBaseChange k Ω).obj X).left ⟶ X.left ↦
          L((t)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj M) (modelFrobenius_left_comp_proj' X N g)) ≫
        (leftDerivedUpperStarComp _ (geometricBaseChangeProj X)
          (g.left ≫ (frobeniusIterate (overFrobenius X) N).left)).hom.app M ≫
        L((geometricBaseChangeProj X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          ((leftDerivedUpperStarComp _ g.left (frobeniusIterate (overFrobenius X) N).left).hom.app
              M ≫
            L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
              ((leftDerivedUpperStarFrobeniusIso ℓ X N).hom.app M)) := by
  simp only [leftDerivedUpperStarModelFrobeniusIso, Iso.trans_hom, NatTrans.comp_app,
    pullbackCongrIso_hom_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.compIsoOfIsoId_hom_app]

variable (Ω) in
/-- The Frobenius comparison `Lπ^* ⋙ LΦ^* ≅ Lg^* ⋙ Lπ^*` of the base change on the ambient
derived categories: `(leftDerivedUpperStarComp Φ π)⁻¹ ≫ leftDerivedUpperStarModelFrobeniusIso`. -/
noncomputable def leftDerivedUpperStarModelFrobeniusComparison :
    L((geometricBaseChangeProj X)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L(((baseChangeModelFrobenius Ω X N g).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ≅
      L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L((geometricBaseChangeProj X)^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  (leftDerivedUpperStarComp _ (baseChangeModelFrobenius Ω X N g).left (geometricBaseChangeProj
      X)).symm ≪≫
    leftDerivedUpperStarModelFrobeniusIso Ω ℓ X N g

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
lemma leftDerivedUpperStarModelFrobeniusComparison_hom_app
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))) :
    (leftDerivedUpperStarModelFrobeniusComparison Ω ℓ X N g).hom.app K =
      (leftDerivedUpperStarComp _ (baseChangeModelFrobenius Ω X N g).left
          (geometricBaseChangeProj X)).inv.app K ≫
        (leftDerivedUpperStarModelFrobeniusIso Ω ℓ X N g).hom.app K :=
  rfl

variable (Ω) in
/-- The Frobenius comparison `b : Lπ^* ⋙ LΦ^* ≅ Lg^* ⋙ Lπ^*` of the base change on bounded
constructible complexes, for the model Frobenius `Φ = (g ≫ F_X^N) ×_k Ω`: the restriction of
`(leftDerivedUpperStarComp Φ π)⁻¹ ≫ leftDerivedUpperStarModelFrobeniusIso`. -/
noncomputable def weilGeometricBaseChangeComparison :
    geometricBaseChangeUpperStar Ω ℓ X ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (baseChangeModelFrobenius
            Ω X N g) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g ⋙
        geometricBaseChangeUpperStar Ω ℓ X :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((leftDerivedUpperStarModelFrobeniusComparison Ω ℓ X N g).app K.obj))
    (fun φ ↦ ObjectProperty.hom_ext _
      ((leftDerivedUpperStarModelFrobeniusComparison Ω ℓ X N g).hom.naturality φ.hom))

/-- The components of the Frobenius comparison of the base change. -/
lemma weilGeometricBaseChangeComparison_hom_app
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilGeometricBaseChangeComparison Ω ℓ X N g).hom.app K =
      (ObjectProperty.isoMk _
        ((leftDerivedUpperStarModelFrobeniusComparison Ω ℓ X N g).app K.obj)).hom :=
  rfl

/-- On the ambient derived category, the Frobenius comparison of the base change is
`(leftDerivedUpperStarComp Φ π)⁻¹ ≫ leftDerivedUpperStarModelFrobeniusIso`. -/
lemma weilGeometricBaseChangeComparison_hom_app_hom
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((weilGeometricBaseChangeComparison Ω ℓ X N g).hom.app K).hom =
      (leftDerivedUpperStarModelFrobeniusComparison Ω ℓ X N g).hom.app K.obj :=
  (congrArg InducedCategory.Hom.hom
    (weilGeometricBaseChangeComparison_hom_app (Ω := Ω) ℓ X N g K)).trans
    ((congrArg InducedCategory.Hom.hom (ObjectProperty.isoMk_hom _ _)).trans
      ((ObjectProperty.homMk_hom _).trans (Iso.app_hom _ _)))

variable (Ω) in
/-- **The base change of Weil objects** from `k` to `Ω`: a Weil object `(K, φ)` of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for an endomorphism `g` of `X` over `Spec k` is sent to the Weil object
`(Lπ^* K, φ̄)` of `Dᵇc(X̄)⟦ℚ̲̄_ℓ⟧` for the model Frobenius `Φ = (g ≫ F_X^N) ×_k Ω`, with
```
φ̄ : LΦ^* Lπ^* K --b--> Lπ^* Lg^* K --Lπ^* φ--> Lπ^* K
```
(`weilGeometricBaseChangeComparison`). For `g = 𝟙` and `Ω` algebraically closed, the model
Frobenius is the base change of the `q^N`-power Frobenius
(`exists_isModelFrobenius_modelFrobenius_id`). -/
noncomputable def weilGeometricBaseChange :
    WeilBoundedConstructible ℓ g ⥤ WeilBoundedConstructible ℓ (baseChangeModelFrobenius Ω X N g) :=
  IsoAlgebra.mapOfNatIso (weilGeometricBaseChangeComparison Ω ℓ X N g)

@[simp]
lemma weilGeometricBaseChange_obj_carrier (K : WeilBoundedConstructible ℓ g) :
    ((weilGeometricBaseChange Ω ℓ X N g).obj K).carrier =
      (geometricBaseChangeUpperStar Ω ℓ X).obj K.carrier :=
  rfl

lemma weilGeometricBaseChange_obj_str (K : WeilBoundedConstructible ℓ g) :
    ((weilGeometricBaseChange Ω ℓ X N g).obj K).str =
      (weilGeometricBaseChangeComparison Ω ℓ X N g).app K.carrier ≪≫
        (geometricBaseChangeUpperStar Ω ℓ X).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ K

end Weil

end AlgebraicGeometry.ProEtale.CondensedRing
