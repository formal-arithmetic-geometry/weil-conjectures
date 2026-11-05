/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CompactCohomology
public import WeilConjectures.TraceFormula.Dualizing

/-!

# Cohomological correspondences and the Lefschetz–Verdier trace formula

Let `X` be a separated `k`-scheme of finite type and `K ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. A *cohomological
endocorrespondence* of `(X, K)` (blueprint `sk-d-corr`) consists of a scheme `C` with two
morphisms `c₁, c₂ : C ⟶ X` and a coefficient map
```
u : Lc₂^* K ⟶ Rc₁^! K
```
(`ProEtale.CondensedRing.Correspondence`). For `c₂` proper it acts on compactly supported
cohomology by the *global operator* (blueprint `def-trf-global-operator`)
```
T_c(u) : RΓ_c(X, K) ⟶ RΓ_c(X, Rc₂_* Lc₂^* K) ≅ RΓ_c(C, Lc₂^* K) --u--> RΓ_c(C, Rc₁^! K)
           ≅ RΓ_c(X, Rc₁_! Rc₁^! K) ⟶ RΓ_c(X, K),
```
the unit of `Lc₂^* ⊣ Rc₂_*`, the identification `Rc₂_* ≅ Rc₂_!`, the composition of the lower
shriek and the counit of `Rc₁_! ⊣ Rc₁^!`
(`ProEtale.CondensedRing.Correspondence.globalOperator`).

The *graph correspondence* of a Weil object `(K, φ)` for `Φ` in degree `m` is
`c_m = (𝟙, Φ_m)` with coefficient map `φ_m : LΦ_m^* K ≅ K ≅ R(𝟙)^! K`
(`ProEtale.CondensedRing.WeilBoundedConstructible.graph`, blueprint
`def-trf-frobenius-coefficient-morphism`).
Its global operator is the global Frobenius `F_{c,m}` obtained from the compactly supported
cohomology of Weil objects
(`ProEtale.CondensedRing.WeilBoundedConstructible.globalOperator_eq_correspondenceGlobalOperator`,
blueprint `prop-trf-graph-frobenius-operator`).

## The Lefschetz–Verdier formula

The *fixed locus* `Fix(c)` of an endocorrespondence is the equalizer of `c₁` and `c₂`
(`ProEtale.CondensedRing.Correspondence.FixedLocus`). The *trace class* of `u` is a Borel–Moore
section `Tr_c(u) : ℚ̄_ℓ,Fix(c) ⟶ ω_Fix(c)` (`ProEtale.CondensedRing.Correspondence.traceClass`,
blueprint `def-trf-trace-class`): the supported pairing of `u` against the diagonal
correspondence `(X, Δ, 1_K)`, through the Künneth–Verdier isomorphism
`RHom(p₂^* K, p₁^! K) ≅ K ⊠ D_X K` and the evaluation `K ⊗ D_X K ⟶ ω_X`. Then:

* for `X` proper and `c₂` proper, `tr(T_c(u) | RΓ_c(X, K)) = ∫_Fix(c) Tr_c(u)`
  (`ProEtale.CondensedRing.Correspondence.trace_globalOperator_eq_integral_traceClass`, blueprint
  `thm-trf-fixed-point-localization`), the Lefschetz–Verdier formula; by
  `BorelMooreSection.integral_eq_sum_localTerm` the right hand side splits into local terms
  along the open and closed pieces of `Fix(c)`
  (blueprint `thm-trf-lefschetz-verdier`);
* over the base point the trace class of an endomorphism `v` integrates to its trace,
  `∫_s Tr(v) = tr(v)` (`ProEtale.CondensedRing.Correspondence.integral_traceClass_ofEnd`,
  blueprint `prop-trf-pairing-point-normalization`);
* on a smooth curve the local term of the Frobenius correspondence at a fixed point is the trace
  of the local Frobenius on the geometric stalk
  (`ProEtale.CondensedRing.WeilBoundedConstructible.localTerm_traceClass_graph_eq_trace`,
  blueprint `thm-trf-frobenius-local-term`). The dualizing complex of the curve enters through
  smooth purity `ω_C ≅ ℚ̄_ℓ,C(1)[2]` (`dualizingComplexSmoothIso`), and that of the reduced
  point components of the fixed locus through the canonical purity for open immersions
  (`BorelMooreSection.restrict`).

The trace class and the theorems about it are in `WeilConjectures.TraceFormula.TraceClass`.

## Main definitions

- `ProEtale.CondensedRing.Correspondence`: an endocorrespondence of `(X, K)`.
- `ProEtale.CondensedRing.Correspondence.globalOperator`: its global operator `T_c(u)`.
- `ProEtale.CondensedRing.Correspondence.ofEnd`: the diagonal correspondence of an endomorphism.
- `ProEtale.CondensedRing.WeilBoundedConstructible.graph`: the Frobenius graph correspondence.
- `ProEtale.CondensedRing.Correspondence.FixedLocus`: the fixed locus, an equalizer of `c₁, c₂`.
- `ProEtale.CondensedRing.Correspondence.ofGraph`: the graph correspondence `(𝟙 X, h)` of a map
  `v : Lh^* K ⟶ K`.
- `ProEtale.CondensedRing.Correspondence.frobeniusGraph`: the graph map in degree `m` of a
  Frobenius coefficient morphism `ψ : LΦ^* K ⟶ K`.

## Main statements

- `ProEtale.CondensedRing.Correspondence.globalOperator_naturality`,
  `ProEtale.CondensedRing.Correspondence.globalOperator_add`: naturality of `T_c(u)` in `(u, K)`
  and linearity in `u` (blueprint `lem-trf-global-operator-naturality`).
- `ProEtale.CondensedRing.Correspondence.nonempty_hasRightDual_globalOperator`: the complexes of
  the definition of `T_c(u)` are perfect (blueprint `lem-trf-global-operator-perfect`).
- `ProEtale.CondensedRing.Correspondence.globalOperator_ofGraph` and its naturality and
  composition laws (blueprint `prop-trf-graph-operator`).
- `ProEtale.CondensedRing.WeilBoundedConstructible.globalOperator_eq_correspondenceGlobalOperator`
  (blueprint `prop-trf-graph-frobenius-operator`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))}

section

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-! ### Correspondences -/

/-- A *cohomological endocorrespondence* of `(X, K)` (blueprint `sk-d-corr`): a separated
`k`-scheme of finite type `C` with morphisms `c₁, c₂ : C ⟶ X`, the support map
`c = (c₁, c₂) : C ⟶ X × X`, and a coefficient map `u : Lc₂^* K ⟶ Rc₁^! K`. The leg `c₂` is the
ordinary pullback leg. -/
structure Correspondence (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) where
  /-- the support `C` of the correspondence. -/
  C : Over (Spec (.of k))
  [locallyOfFiniteType : LocallyOfFiniteType C.hom]
  [quasiCompact : QuasiCompact C.hom]
  [isSeparated : IsSeparated C.hom]
  /-- the exceptional leg `c₁ : C ⟶ X`. -/
  c₁ : C ⟶ X
  /-- the ordinary leg `c₂ : C ⟶ X`. -/
  c₂ : C ⟶ X
  /-- the coefficient map `u : Lc₂^* K ⟶ Rc₁^! K`. -/
  u : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K ⟶
    (boundedConstructibleUpperShriek ℓ c₁).obj K

namespace Correspondence

attribute [instance] locallyOfFiniteType quasiCompact isSeparated

variable {ℓ} {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

/-- The *global operator* `T_c(u)` of an endocorrespondence with proper ordinary leg `c₂` on
compactly supported cohomology `RΓ_c(X, K) = Ra_{X!} K` (blueprint `def-trf-global-operator`,
`sk-d-operator`):
```
Ra_{X!} K ⟶ Ra_{X!} Rc₂_* Lc₂^* K ≅ Ra_{X!} Rc₂_! Lc₂^* K ≅ Ra_{C!} Lc₂^* K
  --Ra_{C!} u--> Ra_{C!} Rc₁^! K ≅ Ra_{X!} Rc₁_! Rc₁^! K ⟶ Ra_{X!} K.
```
-/
noncomputable def globalOperator [IsProper c.c₂.left] :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).obj K ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint X)).obj K :=
  (boundedConstructibleLowerShriek ℓ (toPoint X)).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        c.c₂).unit.app K) ≫
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
        c.c₂).inv.app _) ≫
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c.c₂
      (toPoint X)).inv.app _ ≫
    eqToHom (by rw [comp_toPoint]) ≫
    (boundedConstructibleLowerShriek ℓ (toPoint c.C)).map c.u ≫
    eqToHom (by rw [comp_toPoint]) ≫
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c.c₁
      (toPoint X)).hom.app _ ≫
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
      ((boundedConstructibleUpperShriekAdjunction ℓ
        c.c₁).counit.app K)

/-- The global operator `T_c(u)` in terms of the composition isomorphisms
`Rc_i_! ⋙ Ra_{X!} ≅ Ra_{C!}` (`ProEtale.CondensedRing.boundedConstructibleLowerShriekCompToPoint`):
```
Ra_{X!} K ⟶ Ra_{X!} Rc₂_* Lc₂^* K ≅ Ra_{X!} Rc₂_! Lc₂^* K ≅ Ra_{C!} Lc₂^* K
  --Ra_{C!} u--> Ra_{C!} Rc₁^! K ≅ Ra_{X!} Rc₁_! Rc₁^! K ⟶ Ra_{X!} K.
```
-/
lemma globalOperator_eq [IsProper c.c₂.left] :
    c.globalOperator =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            c.c₂).unit.app K) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ c.c₂).inv.app _) ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ c.c₂).hom.app _ ≫
        (boundedConstructibleLowerShriek ℓ (toPoint c.C)).map
          c.u ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ c.c₁).inv.app _ ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleUpperShriekAdjunction ℓ
            c.c₁).counit.app K) := by
  rw [globalOperator, boundedConstructibleLowerShriekCompToPoint_hom_app,
    boundedConstructibleLowerShriekCompToPoint_inv_app]
  simp only [Category.assoc]

variable (K) in
/-- The global operator of the correspondence with support `C`, legs `c₁, c₂` and coefficient
map `u`, as an explicit composite of its fields (see `globalOperator_eq_globalOperatorMk`). -/
noncomputable def globalOperatorMk (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom]
    [QuasiCompact C.hom] [IsSeparated C.hom] (c₁ c₂ : C ⟶ X) [IsProper c₂.left]
    (u : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K ⟶
      (boundedConstructibleUpperShriek ℓ c₁).obj K) :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).obj K ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint X)).obj K :=
  (boundedConstructibleLowerShriek ℓ (toPoint X)).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        c₂).unit.app K) ≫
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ c₂).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K)) ≫
    (boundedConstructibleLowerShriekCompToPoint ℓ c₂).hom.app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K) ≫
    (boundedConstructibleLowerShriek ℓ (toPoint C)).map u ≫
    (boundedConstructibleLowerShriekCompToPoint ℓ c₁).inv.app
      ((boundedConstructibleUpperShriek ℓ c₁).obj K) ≫
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
      ((boundedConstructibleUpperShriekAdjunction ℓ
        c₁).counit.app K)

lemma globalOperator_eq_globalOperatorMk [IsProper c.c₂.left] :
    c.globalOperator = globalOperatorMk K c.C c.c₁ c.c₂ c.u := by
  rw [globalOperator_eq, globalOperatorMk]

/-- `globalOperator_eq_globalOperatorMk` for a correspondence given by its fields. -/
lemma globalOperator_mk (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom]
    [QuasiCompact C.hom] [IsSeparated C.hom] (c₁ c₂ : C ⟶ X) [IsProper c₂.left]
    (u : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K ⟶
      (boundedConstructibleUpperShriek ℓ c₁).obj K) :
    (⟨C, c₁, c₂, u⟩ : Correspondence ℓ K).globalOperator = globalOperatorMk K C c₁ c₂ u :=
  globalOperator_eq_globalOperatorMk _

/-! ### Graph correspondences -/

/-- The counit of `R(𝟙 X)_! ⊣ R(𝟙 X)^!` is the identity, up to the identity isomorphisms. -/
lemma boundedConstructibleUpperShriekAdjunction_id_counit_app
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 X)).counit.app
        M =
      (boundedConstructibleLowerShriekId ℓ X).hom.app
          ((boundedConstructibleUpperShriek ℓ (𝟙 X)).obj M) ≫
        (boundedConstructibleUpperShriekId ℓ X).hom.app M := by
  have h := conjugateEquiv_counit
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 X))
    Adjunction.id (boundedConstructibleLowerShriekId ℓ X).inv M
  rw [boundedConstructibleUpperShriekId, conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    ← cancel_epi ((boundedConstructibleLowerShriekId ℓ X).inv.app
      ((boundedConstructibleUpperShriek ℓ (𝟙 X)).obj M)),
    Iso.inv_hom_id_app_assoc]
  exact h.symm.trans (Category.comp_id _)

/-- The global operator of a correspondence whose exceptional leg is the identity,
`c = (𝟙 X, h)`: it is `RΓ_c(X, u) ∘ h^♯` after `R(𝟙 X)^! ≅ 𝟭`. -/
theorem globalOperator_mk_id (h : X ⟶ X) [IsProper h.left]
    (u : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶
      (boundedConstructibleUpperShriek ℓ (𝟙 X)).obj K) :
    (⟨X, 𝟙 X, h, u⟩ : Correspondence ℓ K).globalOperator =
      (compactPullback ℓ h).app K ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          (u ≫ (boundedConstructibleUpperShriekId ℓ X).hom.app K) := by
  have hl := boundedConstructibleLowerShriekComp_padicAlgCl_id_left ℓ (toPoint X)
    ((boundedConstructibleUpperShriek ℓ (𝟙 X)).obj K)
  simp only [Functor.map_comp] at hl
  rw [globalOperator_mk, globalOperatorMk, boundedConstructibleUpperShriekAdjunction_id_counit_app,
    compactPullback_app, boundedConstructibleLowerShriekCompToPoint_inv_app]
  simp only [boundedConstructibleLowerShriekId, Iso.trans_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hl, eqToHom_trans_assoc]
  simp only [eqToHom_refl, Category.id_comp]

variable (K) in
/-- The *graph correspondence* `(X, 𝟙 X, h, v)` of an endomorphism `h : X ⟶ X` and a map
`v : Lh^* K ⟶ K`, with coefficient map `Lh^* K --v--> K ≅ R(𝟙 X)^! K` (blueprint
`prop-trf-graph-operator`). -/
noncomputable def ofGraph (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K) :
    Correspondence ℓ K where
  C := X
  c₁ := 𝟙 X
  c₂ := h
  u := v ≫ (boundedConstructibleUpperShriekId ℓ X).inv.app K

instance (h : X ⟶ X) [IsProper h.left]
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K) :
    IsProper (ofGraph K h v).c₂.left :=
  inferInstanceAs (IsProper h.left)

/-- **The global operator of a graph correspondence** (blueprint `prop-trf-graph-operator`): for
a proper `h`, `T_{(𝟙, h)}(v)` is the composite
```
RΓ_c(X, K) --h^♯--> RΓ_c(X, Lh^* K) --RΓ_c(X, v)--> RΓ_c(X, K),
```
where `h^♯` is induced by the unit `K ⟶ Rh_* Lh^* K` and `Rh_* ≅ Rh_!`
(`ProEtale.CondensedRing.compactPullback`). -/
theorem globalOperator_ofGraph (h : X ⟶ X) [IsProper h.left]
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K) :
    (ofGraph K h v).globalOperator =
      (compactPullback ℓ h).app K ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map v := by
  refine (globalOperator_mk_id h _).trans ?_
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id]

variable (K) in
/-- The *diagonal correspondence* `(X, 𝟙, 𝟙, v)` of an endomorphism `v : K ⟶ K`, with
coefficient map `L(𝟙)^* K ≅ K --v--> K ≅ R(𝟙)^! K`. -/
noncomputable def ofEnd (v : K ⟶ K) : Correspondence ℓ K where
  C := X
  c₁ := 𝟙 X
  c₂ := 𝟙 X
  u := (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K ≫ v ≫
    (boundedConstructibleUpperShriekId ℓ X).inv.app K

instance (v : K ⟶ K) : IsProper (ofEnd K v).c₂.left :=
  inferInstanceAs (IsProper (𝟙 X.left))

/-! ### The fixed locus and the trace class -/

/-- The *fixed locus* `Fix(c) = C ×_{X × X} X` of an endocorrespondence: an equalizer
`ι : Fix(c) ⟶ C` of the two legs `c₁` and `c₂` in `Over (Spec (.of k))` (blueprint `sk-d-corr`). -/
structure FixedLocus where
  /-- the fixed scheme `Fix(c)`. -/
  F : Over (Spec (.of k))
  [locallyOfFiniteType : LocallyOfFiniteType F.hom]
  [quasiCompact : QuasiCompact F.hom]
  [isSeparated : IsSeparated F.hom]
  /-- the inclusion `ι : Fix(c) ⟶ C`. -/
  ι : F ⟶ c.C
  w : ι ≫ c.c₁ = ι ≫ c.c₂
  /-- `ι` is an equalizer of `c₁` and `c₂`. -/
  isLimit : IsLimit (Fork.ofι ι w)

attribute [instance] FixedLocus.locallyOfFiniteType FixedLocus.quasiCompact
  FixedLocus.isSeparated

/-- The fixed locus of a diagonal correspondence is the whole scheme. -/
noncomputable def fixedLocusOfEnd (v : K ⟶ K) : (ofEnd K v).FixedLocus where
  F := X
  ι := 𝟙 X
  w := rfl
  isLimit := Fork.IsLimit.mk _ (fun s ↦ s.ι) (fun _ ↦ Category.comp_id _)
    (fun _ _ hm ↦ by simpa using hm)

end Correspondence

end

/-! ### The Frobenius graph correspondence -/

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace WeilBoundedConstructible

variable {ℓ} {Φ : X ⟶ X}

/-- The *graph correspondence* `c_m = (𝟙, Φ_m)` of a Weil object `(K, φ)` in degree `m`, with
coefficient map `LΦ_m^* K --φ_m--> K ≅ R(𝟙 X)^! K` (blueprint
`def-trf-frobenius-coefficient-morphism`). -/
noncomputable def graph (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) :
    Correspondence ℓ K.carrier where
  C := X
  c₁ := 𝟙 X
  c₂ := frobeniusIterate Φ m
  u := (K.iterateStr m).hom ≫ (boundedConstructibleUpperShriekId ℓ X).inv.app K.carrier

instance (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) [IsFinite (frobeniusIterate Φ m).left] :
    IsProper (K.graph m).c₂.left :=
  inferInstanceAs (IsProper (frobeniusIterate Φ m).left)

/-- **The global operator of the graph correspondence** (blueprint
`prop-trf-graph-frobenius-operator`): the global Frobenius `F_{c,m}` defined through the
compactly supported cohomology of Weil objects is the global operator `T_{c_m}(φ_m)` of the
graph correspondence `c_m = (𝟙, Φ_m)`. -/
theorem globalOperator_eq_correspondenceGlobalOperator (K : WeilBoundedConstructible ℓ Φ)
    (m : ℕ) [IsFinite (frobeniusIterate Φ m).left]
    [IsUniversalHomeomorphism (frobeniusIterate Φ m).left] :
    K.globalOperator m = (K.graph m).globalOperator :=
  (WeilBoundedConstructible.globalOperator_eq K m).trans
    (Correspondence.globalOperator_ofGraph _ _).symm

/-- A rational point `x` fixed by `Φ_m` lies on the fixed locus of the graph correspondence
`c_m`: the factorization of `x` through the equalizer `Fix(c_m) ⟶ X` of `𝟙` and `Φ_m`. -/
noncomputable def fixedLocusPoint (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (F : (K.graph m).FixedLocus) (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) :
    RationalPoint F.F :=
  F.isLimit.lift (Fork.ofι (P := point k) x (by
    change x ≫ 𝟙 X = x ≫ frobeniusIterate Φ m
    rw [Category.comp_id, hx]))

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
