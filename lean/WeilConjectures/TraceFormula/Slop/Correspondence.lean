/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Slop.CompactCohomology
public import WeilConjectures.TraceFormula.Slop.Dualizing

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
  point components of the fixed locus through étale purity (`BorelMooreSection.restrict`).

## Sorried data

`ProEtale.CondensedRing.Correspondence.traceClass` is stated as a definition with value
`sorry`: its construction needs the external tensor product and the Künneth–Verdier
isomorphism on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`, which are not available yet.

## Main definitions

- `ProEtale.CondensedRing.Correspondence`: an endocorrespondence of `(X, K)`.
- `ProEtale.CondensedRing.Correspondence.globalOperator`: its global operator `T_c(u)`.
- `ProEtale.CondensedRing.Correspondence.ofEnd`: the diagonal correspondence of an endomorphism.
- `ProEtale.CondensedRing.WeilBoundedConstructible.graph`: the Frobenius graph correspondence.
- `ProEtale.CondensedRing.Correspondence.FixedLocus`: the fixed locus, an equalizer of `c₁, c₂`.
- `ProEtale.CondensedRing.Correspondence.traceClass`: the trace class `Tr_c(u)`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

namespace Slop
end Slop
open Slop


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
structure Slop.Correspondence (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) where
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
    (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ c₁).obj K

namespace Slop.Correspondence

attribute [instance] locallyOfFiniteType quasiCompact isSeparated

variable {ℓ} {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

/-- The *global operator* `T_c(u)` of an endocorrespondence with proper ordinary leg `c₂` on
compactly supported cohomology `RΓ_c(X, K) = Ra_{X!} K` (blueprint `def-trf-global-operator`):
```
Ra_{X!} K ⟶ Ra_{X!} Rc₂_* Lc₂^* K ≅ Ra_{X!} Rc₂_! Lc₂^* K ≅ Ra_{C!} Lc₂^* K
  --Ra_{C!} u--> Ra_{C!} Rc₁^! K ≅ Ra_{X!} Rc₁_! Rc₁^! K ⟶ Ra_{X!} K.
```
-/
noncomputable def globalOperator [IsProper c.c₂.left] :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj K ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj K :=
  (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
      ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
        c.c₂).unit.app K) ≫
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
        c.c₂).inv.app _) ≫
    (boundedConstructibleLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂
      (toPoint X)).inv.app _ ≫
    eqToHom (by rw [comp_toPoint]) ≫
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint c.C)).map c.u ≫
    eqToHom (by rw [comp_toPoint]) ≫
    (boundedConstructibleLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ c.c₁
      (toPoint X)).hom.app _ ≫
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
      ((boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
        c.c₁).counit.app K)

variable (K) in
/-- The *diagonal correspondence* `(X, 𝟙, 𝟙, v)` of an endomorphism `v : K ⟶ K`, with
coefficient map `L(𝟙)^* K ≅ K --v--> K ≅ R(𝟙)^! K`. -/
noncomputable def ofEnd (v : K ⟶ K) : Correspondence ℓ K where
  C := X
  c₁ := 𝟙 X
  c₂ := 𝟙 X
  u := (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K ≫ v ≫
    (boundedConstructibleUpperShriekId ℓ X).inv.app K

instance Slop.instCorrespondence1 (v : K ⟶ K) : IsProper (ofEnd K v).c₂.left :=
  inferInstanceAs (IsProper (𝟙 X.left))

/-- The global operator of the diagonal correspondence of `v` is `RΓ_c(X, v)`. -/
theorem globalOperator_ofEnd (v : K ⟶ K) :
    (ofEnd K v).globalOperator =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map v :=
  sorry

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

/-- The *trace class* `Tr_c(u) : ℚ̄_ℓ,Fix(c) ⟶ ω_Fix(c)` of an endocorrespondence (blueprint
`def-trf-trace-class`): the supported pairing `⟨u, 1_K⟩_LV` of `u` against the diagonal
identity, carried out over the cartesian square `Fix(c) = C ×_{X × X} X`. It is the restriction
to `Fix(c)` of the class of `u` in
`Hom(Lc^* (K ⊠ D_X K), Rc^! ω_{X × X})`, through the Künneth–Verdier isomorphism and the
Verdier evaluation `K ⊗ D_X K ⟶ ω_X` (blueprint `lem-trf-trace-map-from-external-duality`).
See the module docstring for why it is sorried. -/
@[no_expose]
noncomputable def traceClass (F : c.FixedLocus) : BorelMooreSection ℓ F.F :=
  sorry

/-- The fixed locus of a diagonal correspondence is the whole scheme. -/
noncomputable def fixedLocusOfEnd (v : K ⟶ K) : (ofEnd K v).FixedLocus where
  F := X
  ι := 𝟙 X
  w := rfl
  isLimit := Fork.IsLimit.mk _ (fun s ↦ s.ι) (fun _ ↦ Category.comp_id _)
    (fun _ _ hm ↦ by simpa using hm)

end Slop.Correspondence

end

namespace Slop.Correspondence

variable {ℓ} [QuasiCompact X.hom] [IsProper X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

attribute [local instance] boundedConstructibleBraiding in
/-- **The Lefschetz–Verdier formula** (blueprint `thm-trf-fixed-point-localization`): for `X`
proper over `s`, an endocorrespondence `c` with proper ordinary leg `c₂` and proper fixed locus,
the trace of the global operator is the integral of the trace class,
`tr(T_c(u) | RΓ_c(X, K)) = ∫_Fix(c) Tr_c(u)`. -/
theorem trace_globalOperator_eq_integral_traceClass [IsProper c.c₂.left]
    (F : c.FixedLocus) [IsProper F.F.hom]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj K)] :
    trace c.globalOperator = (c.traceClass F).integral :=
  sorry

instance Slop.instCorrespondence2 (v : K ⟶ K) : IsProper (fixedLocusOfEnd v).F.hom :=
  inferInstanceAs (IsProper X.hom)

attribute [local instance] boundedConstructibleBraiding in
/-- **Point normalization of the pairing** (blueprint `prop-trf-pairing-point-normalization`):
over the base point, the trace class of the diagonal correspondence of an endomorphism `v` of
a perfect complex integrates to the categorical trace of `v`, `∫_s Tr(v) = tr(v)`. -/
theorem integral_traceClass_ofEnd {K : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    [HasRightDual K] (v : K ⟶ K) :
    ((ofEnd K v).traceClass (fixedLocusOfEnd v)).integral = trace v :=
  sorry

end Slop.Correspondence

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

instance Slop.instCorrespondence3 (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) [IsFinite (frobeniusIterate Φ m).left] :
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
  sorry

/-- A rational point `x` fixed by `Φ_m` lies on the fixed locus of the graph correspondence
`c_m`: the factorization of `x` through the equalizer `Fix(c_m) ⟶ X` of `𝟙` and `Φ_m`. -/
noncomputable def fixedLocusPoint (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    (F : (K.graph m).FixedLocus) (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x) :
    RationalPoint F.F :=
  F.isLimit.lift (Fork.ofι (P := point k) x (by
    change x ≫ 𝟙 X = x ≫ frobeniusIterate Φ m
    rw [Category.comp_id, hx]))

attribute [local instance] boundedConstructibleBraiding in
/-- **The local term of the Frobenius correspondence on a curve** (blueprint
`thm-trf-frobenius-local-term`): let `X` be smooth of relative dimension one over `s` with the
model Frobenius `Φ` of a model `X₀` over a finite field, let `x` be a rational point fixed by
`Φ_m` and let `j : B ⟶ Fix(c_m)` be an open and closed subscheme of the fixed locus of the graph
correspondence, proper over `s`, whose underlying set is the point `x`. Then the local term of
the trace class of `φ_m` along `B` is the trace of the local Frobenius `F_{x,m}` on the
geometric stalk `K_x̄`. No local constancy of `K` at `x` is assumed. -/
theorem localTerm_traceClass_graph_eq_trace [SmoothOfRelativeDimension 1 X.hom]
    {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
    {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} (hΦ : IsModelFrobenius Φ f₀ p)
    (K : WeilBoundedConstructible ℓ Φ) {m : ℕ} (hm : 1 ≤ m) (F : (K.graph m).FixedLocus)
    [IsProper F.F.hom] (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x)
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(K.fixedLocusPoint m F x hx).left.base (default : Spec (.of k))})
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      K.carrier)] :
    ((K.graph m).traceClass F).localTerm j = trace (K.stalkFrobenius m x hx) :=
  sorry

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
