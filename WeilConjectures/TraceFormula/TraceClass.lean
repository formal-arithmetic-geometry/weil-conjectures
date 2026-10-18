/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExceptionalHom
public import WeilConjectures.TraceFormula.KunnethVerdier
public import WeilConjectures.TraceFormula.LocalTerm

/-!

# The trace class of a cohomological correspondence

Let `c = (C, c₁, c₂, u)` be an endocorrespondence of `(X, K)`, with support map
`c = (c₁, c₂) : C ⟶ X ⨯ X`, fixed locus `ι : Fix(c) ⟶ C` and `d = ι ≫ c₁ : Fix(c) ⟶ X`, so that
the fixed square `ι ≫ c = d ≫ Δ_X` is cartesian (`Correspondence.FixedLocus.isPullback`). The
*trace class* of `u` is the Borel–Moore section (blueprint `def-trf-trace-class`,
`sk-d-trace-class`)
```
Tr_c(u) : ℚ̄_ℓ,Fix(c) ⟶ ω_Fix(c)
```
(`ProEtale.CondensedRing.Correspondence.traceClass`), the `Lι^* ⊣ Rι_*` adjoint of
```
ℚ̄_ℓ,C --ũ--> 𝓗_c(K) --𝔱--> Rι_* ω_Fix(c),
```
where
* `𝓗_c(K) = RHom(Lc₂^* K, Rc₁^! K)` is the *trace-class source* and `ũ` the mate of `u`
  (`Correspondence.traceClassSource`, `Correspondence.mate`, blueprint
  `def-trf-trace-class-source`);
* `𝔱` is the *trace morphism from external duality* (`Correspondence.traceMap`, blueprint
  `lem-trf-trace-map-from-external-duality`):
  ```
  𝓗_c(K) ≅ Rc^! (K ⊠ D_X K) --Rc^! e_K--> Rc^! RΔ_* ω_X ≅ Rι_* Rd^! ω_X ≅ Rι_* ω_Fix(c),
  ```
  the external duality isomorphism (`Correspondence.verdierDualityIso`, blueprint
  `thm-trf-verdier-duality`: the exceptional internal hom exchange
  `RHom(Lc^* M, Rc^! N) ≅ Rc^! RHom(M, N)` of blueprint
  `lem-trf-exceptional-internal-hom-exchange` followed by the inverse Künneth–Verdier map), the
  evaluation kernel `e_K : K ⊠ D_X K ⟶ RΔ_* ω_X` adjoint to the evaluation
  `K ⊗ D_X K ⟶ ω_X` (`evaluationKernel`), the right-adjoint form of compact-support base change
  in the fixed square (`Correspondence.FixedLocus.upperShriekLowerStarIso`, blueprint
  `thm-trf-fixed-point-base-change`) and the composition isomorphism `Rd^! ω_X ≅ ω_Fix(c)` of
  the dualizing complexes.

The construction uses the derived projection formula (blueprint `thm-sf-pf-proetale`), compact
support base change and the Künneth–Verdier theorem (blueprint `thm-trf-kunneth-verdier`) only
through the invertibility of the canonical maps; it needs no further hypothesis on `c` or `K`
(blueprint `prop-trf-trace-class-unconditional`).

## Main statements

- `ProEtale.CondensedRing.Correspondence.trace_globalOperator_eq_integral_traceClass`: the
  Lefschetz–Verdier formula `tr(T_c(u) | RΓ_c(X, K)) = ∫_Fix(c) Tr_c(u)` for `X` proper.
- `ProEtale.CondensedRing.Correspondence.integral_traceClass_ofEnd`: over the base point,
  `∫_s Tr(v) = tr(v)`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.localTerm_traceClass_graph_eq_trace`: on a
  smooth curve, the local term of the Frobenius correspondence at a fixed point is the trace of
  the local Frobenius.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))}

/-! ### Internal homs along isomorphisms -/

section IhomIso

variable {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞] [MonoidalClosed 𝒞]

/-- The isomorphism `RHom(A, B) ≅ RHom(A', B')` induced by isomorphisms `A ≅ A'` and
`B ≅ B'`. -/
noncomputable def ihomIsoOfIso {A A' B B' : 𝒞} (eA : A ≅ A') (eB : B ≅ B') :
    (ihom A).obj B ≅ (ihom A').obj B' :=
  (ihom A).mapIso eB ≪≫ (internalHom.mapIso eA.symm.op).app B'

end IhomIso

/-! ### Evaluation kernels -/

section Evaluation

variable (ℓ) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The identification `LΔ_X^* (K ⊠ N) ≅ K ⊗ N` of the restriction of an external product to the
diagonal: the monoidal structure of `LΔ_X^*` and `L(Δ_X ≫ p_i)^* = L(𝟙)^* ≅ 𝟭`. -/
noncomputable def diagUpperStarExternalProductIso
    (K N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ (diag X)).obj (externalProduct ℓ K N) ≅ K ⊗ N :=
  (Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ (diag X)) _ _).symm ≪≫
    tensorIso
      (((boundedConstructibleUpperStarComp _ ℓ (diag X) prod.fst).app K).symm ≪≫
        eqToIso (by rw [diag, prod.lift_fst]) ≪≫
        (boundedConstructibleUpperStarId _ ℓ X).app K)
      (((boundedConstructibleUpperStarComp _ ℓ (diag X) prod.snd).app N).symm ≪≫
        eqToIso (by rw [diag, prod.lift_snd]) ≪≫
        (boundedConstructibleUpperStarId _ ℓ X).app N)

/-- The *evaluation kernel* `e_K : K ⊠ D_X K ⟶ RΔ_* ω_X` (blueprint
`lem-trf-trace-map-from-external-duality`, `def-trf-kernel-pushforward-maps`): the
`LΔ^* ⊣ RΔ_*` adjoint of the evaluation `LΔ^* (K ⊠ D_X K) ≅ K ⊗ D_X K ⟶ ω_X`. -/
noncomputable def evaluationKernel (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ K (verdierDual ℓ (toPoint X) K) ⟶
      (boundedConstructibleLowerStar _ ℓ (diag X)).obj (dualizingComplex ℓ X) :=
  (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (diag X)).homEquiv _ _
    ((diagUpperStarExternalProductIso ℓ K _).hom ≫ (ihom.ev K).app (dualizingComplex ℓ X))

end Evaluation

/-! ### The class of a correspondence -/

section CorrespondenceClass

variable (ℓ) {C Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom] (c : C ⟶ Y ⨯ X)

/-- **The class of a correspondence** (blueprint `lem-trf-correspondence-class`): for the support
`c = (c₁, c₂) : C ⟶ Z = Y ⨯ X` of a correspondence from `(X, K)` to `(Y, L)`, with
`c₁ = c ≫ p₁` and `c₂ = c ≫ p₂`, the tensor–hom adjunction, the derived projection formula for
`c` and the exceptional adjunction give a bijection
```
Hom(Rc_! ℚ̄_ℓ,C, RHom(Lp₂^* K, Rp₁^! L)) ≃ Hom(Lc₂^* K, Rc₁^! L),
```
natural in `K` and `L` (`correspondenceClassEquiv_naturality_left`,
`correspondenceClassEquiv_naturality_right`). The *class* `[u]` of a coefficient map `u` is its
inverse image, a class supported on `c`. -/
noncomputable def correspondenceClassEquiv (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerShriek _ ℓ c).obj (𝟙_ _) ⟶
        (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek _ ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj L)) ≃
      ((boundedConstructibleUpperStar _ ℓ (c ≫ prod.snd)).obj K ⟶
        (boundedConstructibleUpperShriek _ ℓ (c ≫ prod.fst)).obj L) where
  toFun g := (boundedConstructibleUpperStarComp _ ℓ c prod.snd).hom.app K ≫
    Verdier.correspondenceClassEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ c)
      (boundedConstructibleExceptionalProjection _ ℓ c) _ _ g ≫
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst).inv.app L
  invFun f := (Verdier.correspondenceClassEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ c)
      (boundedConstructibleExceptionalProjection _ ℓ c) _ _).symm
    ((boundedConstructibleUpperStarComp _ ℓ c prod.snd).inv.app K ≫ f ≫
      (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst).hom.app L)
  left_inv g := by
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id,
      Iso.inv_hom_id_app_assoc, Equiv.symm_apply_apply]
  right_inv f := by
    simp only [Equiv.apply_symm_apply, Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id, Iso.hom_inv_id_app_assoc]

lemma correspondenceClassEquiv_apply (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (g : (boundedConstructibleLowerShriek _ ℓ c).obj (𝟙_ _) ⟶
        (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek _ ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj L)) :
    correspondenceClassEquiv ℓ c K L g =
      (boundedConstructibleUpperStarComp _ ℓ c prod.snd).hom.app K ≫
        Verdier.correspondenceClassEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ c)
          (boundedConstructibleExceptionalProjection _ ℓ c) _ _ g ≫
        (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst).inv.app L :=
  rfl

/-- Naturality of the class bijection in `L` (blueprint `lem-trf-correspondence-class`). -/
lemma correspondenceClassEquiv_naturality_right
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {L L' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (b : L ⟶ L')
    (g : (boundedConstructibleLowerShriek _ ℓ c).obj (𝟙_ _) ⟶
        (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek _ ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj L)) :
    correspondenceClassEquiv ℓ c K L'
        (g ≫ (ihom _).map ((boundedConstructibleUpperShriek _ ℓ prod.fst).map b)) =
      correspondenceClassEquiv ℓ c K L g ≫
        (boundedConstructibleUpperShriek _ ℓ (c ≫ prod.fst)).map b := by
  exact Verdier.correspondenceClassEquiv_naturality_right_conj
    (boundedConstructibleUpperShriekAdjunction _ ℓ c)
    (boundedConstructibleExceptionalProjection _ ℓ c) _
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst)
    ((boundedConstructibleUpperStarComp _ ℓ c prod.snd).hom.app K) b g

/-- Naturality of the class bijection in `K` (blueprint `lem-trf-correspondence-class`). -/
lemma correspondenceClassEquiv_naturality_left
    {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (a : K' ⟶ K)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (g : (boundedConstructibleLowerShriek _ ℓ c).obj (𝟙_ _) ⟶
        (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek _ ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj L)) :
    correspondenceClassEquiv ℓ c K' L
        (g ≫ (pre ((boundedConstructibleUpperStar _ ℓ prod.snd).map a)).app _) =
      (boundedConstructibleUpperStar _ ℓ (c ≫ prod.snd)).map a ≫
        correspondenceClassEquiv ℓ c K L g := by
  exact Verdier.correspondenceClassEquiv_naturality_left_conj
    (boundedConstructibleUpperShriekAdjunction _ ℓ c)
    (boundedConstructibleExceptionalProjection _ ℓ c) _
    (boundedConstructibleUpperStarComp _ ℓ c prod.snd)
    ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst).inv.app L) a g

end CorrespondenceClass

/-! ### The trace class -/

namespace Correspondence

section

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

/-- The *trace-class source* `𝓗_c(K) = RHom(Lc₂^* K, Rc₁^! K)` of an endocorrespondence
(blueprint `def-trf-trace-class-source`). -/
noncomputable def traceClassSource : Dᵇc(c.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (ihom ((boundedConstructibleUpperStar _ ℓ c.c₂).obj K)).obj
    ((boundedConstructibleUpperShriek _ ℓ c.c₁).obj K)

/-- The *mate* `ũ : ℚ̄_ℓ,C ⟶ 𝓗_c(K)` of the coefficient map `u`, its transpose under the
tensor–hom adjunction (blueprint `def-trf-trace-class-source`). -/
noncomputable def mate : 𝟙_ _ ⟶ c.traceClassSource :=
  Verdier.homMate c.u

/-- The mate construction identifies coefficient maps `Lc₂^* K ⟶ Rc₁^! K` with sections of the
trace-class source (blueprint `def-trf-trace-class-source`). -/
noncomputable def mateEquiv :
    ((boundedConstructibleUpperStar _ ℓ c.c₂).obj K ⟶
        (boundedConstructibleUpperShriek _ ℓ c.c₁).obj K) ≃
      (𝟙_ _ ⟶ c.traceClassSource) :=
  Verdier.homMateEquiv _ _

lemma mateEquiv_apply_u : c.mateEquiv c.u = c.mate :=
  rfl

/-- The **exceptional internal hom exchange** for the support map (blueprint
`lem-trf-exceptional-internal-hom-exchange`): for `M, N` on `X ⨯ X`,
`RHom(Lc^* M, Rc^! N) ≅ Rc^! RHom(M, N)`, built from the derived projection formula for `c`
and the two adjunctions. -/
noncomputable def exceptionalHomIso (M N : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (ihom ((boundedConstructibleUpperStar _ ℓ c.support).obj M)).obj
        ((boundedConstructibleUpperShriek _ ℓ c.support).obj N) ≅
      (boundedConstructibleUpperShriek _ ℓ c.support).obj ((ihom M).obj N) :=
  haveI := Verdier.isIso_exceptionalHomMap_of_isIso
    (boundedConstructibleUpperShriekAdjunction _ ℓ c.support)
    (boundedConstructibleExceptionalProjection _ ℓ c.support) M N
  asIso (Verdier.exceptionalHomMap (boundedConstructibleUpperShriekAdjunction _ ℓ c.support)
    (boundedConstructibleExceptionalProjection _ ℓ c.support) M N)

/-- The trace-class source in terms of the support map:
`RHom(Lc₂^* K, Rc₁^! K) ≅ RHom(Lc^* Lp₂^* K, Rc^! Rp₁^! K)`, by the composition isomorphisms
for `c₂ = c ≫ p₂` and `c₁ = c ≫ p₁`. -/
noncomputable def traceClassSourceIso :
    c.traceClassSource ≅
      (ihom ((boundedConstructibleUpperStar _ ℓ c.support).obj
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj K))).obj
        ((boundedConstructibleUpperShriek _ ℓ c.support).obj
          ((boundedConstructibleUpperShriek _ ℓ (prod.fst : X ⨯ X ⟶ X)).obj K)) :=
  ihomIsoOfIso
    (eqToIso (by rw [support_snd]) ≪≫
      (boundedConstructibleUpperStarComp _ ℓ c.support prod.snd).app K)
    (eqToIso (by rw [support_fst]) ≪≫
      (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c.support prod.fst).app K)

/-- The **external duality isomorphism** of the trace-class source (blueprint
`thm-trf-verdier-duality`): `𝓗_c(K) ≅ Rc^! (K ⊠ D_X K)`, the exceptional internal hom exchange
`RHom(Lc^* Lp₂^* K, Rc^! Rp₁^! K) ≅ Rc^! RHom(Lp₂^* K, Rp₁^! K)` followed by `Rc^!` of the
inverse Künneth–Verdier isomorphism `κ_{K,K}`. -/
noncomputable def verdierDualityIso :
    c.traceClassSource ≅
      (boundedConstructibleUpperShriek _ ℓ c.support).obj
        (externalProduct ℓ K (verdierDual ℓ (toPoint X) K)) :=
  c.traceClassSourceIso ≪≫ c.exceptionalHomIso _ _ ≪≫
    (boundedConstructibleUpperShriek _ ℓ c.support).mapIso
      (asIso (kunnethVerdierMap ℓ K K)).symm

namespace FixedLocus

variable {c} (F : c.FixedLocus)

/-- **Base change in the fixed square** (blueprint `thm-trf-fixed-point-base-change`, (2)):
compact-support base change `LΔ_X^* Rc_! ≅ Rd_! Lι^*` in the cartesian fixed square. -/
noncomputable def lowerShriekBaseChangeIso :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ c.support ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ F.d :=
  haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ F.isPullback
  asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ F.isPullback)

/-- **Base change in the fixed square, right-adjoint form** (blueprint
`thm-trf-fixed-point-base-change`, (2)): `Rc^! RΔ_{X*} ≅ Rι_* Rd^!`, the conjugate of
`lowerShriekBaseChangeIso` for the composite adjunctions `Rc_! ⋙ LΔ^* ⊣ RΔ_* ⋙ Rc^!` and
`Lι^* ⋙ Rd_! ⊣ Rd^! ⋙ Rι_*`. -/
noncomputable def upperShriekLowerStarIso :
    boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X) ⋙
        boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ c.support ≅
      boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ F.d ⋙
        boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι :=
  conjugateIsoEquiv
    ((boundedConstructibleUpperShriekAdjunction _ ℓ c.support).comp
      (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (diag X)))
    ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ F.ι).comp
      (boundedConstructibleUpperShriekAdjunction _ ℓ F.d))
    F.lowerShriekBaseChangeIso.symm

/-- **Pullback along the ordinary leg in the fixed square** (blueprint
`thm-trf-fixed-point-base-change`, (1)): `Lι^* Lc₂^* K ≅ Ld^* K`, from `ι ≫ c₂ = d`. -/
noncomputable def upperStarC₂Iso (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ F.ι).obj ((boundedConstructibleUpperStar _ ℓ c.c₂).obj K) ≅
      (boundedConstructibleUpperStar _ ℓ F.d).obj K :=
  ((boundedConstructibleUpperStarComp _ ℓ F.ι c.c₂).app K).symm ≪≫
    eqToIso (by rw [F.ι_c₂])

end FixedLocus

/-- The *trace morphism from external duality* `𝔱 : 𝓗_c(K) ⟶ Rι_* ω_Fix(c)` (blueprint
`lem-trf-trace-map-from-external-duality`, objectwise form):
```
𝓗_c(K) ≅ Rc^! (K ⊠ D_X K) --Rc^! e_K--> Rc^! RΔ_* ω_X ≅ Rι_* Rd^! ω_X ≅ Rι_* ω_Fix(c).
```
-/
noncomputable def traceMap (F : c.FixedLocus) :
    c.traceClassSource ⟶
      (boundedConstructibleLowerStar _ ℓ F.ι).obj (dualizingComplex ℓ F.F) :=
  c.verdierDualityIso.hom ≫
    (boundedConstructibleUpperShriek _ ℓ c.support).map (evaluationKernel ℓ K) ≫
    (F.upperShriekLowerStarIso.app (dualizingComplex ℓ X)).hom ≫
    (boundedConstructibleLowerStar _ ℓ F.ι).map (dualizingComplexComp ℓ F.d).hom

/-- The *trace class* `Tr_c(u) : ℚ̄_ℓ,Fix(c) ⟶ ω_Fix(c)` of an endocorrespondence (blueprint
`def-trf-trace-class`, `sk-d-trace-class`): the `Lι^* ⊣ Rι_*` adjoint of the composite
`ℚ̄_ℓ,C --ũ--> 𝓗_c(K) --𝔱--> Rι_* ω_Fix(c)` of the mate of `u` and the trace morphism
`traceMap`, read through `ℚ̄_ℓ,Fix(c) ≅ Lι^* ℚ̄_ℓ,C`. It is defined for every correspondence,
with no hypothesis beyond the finiteness conditions on the schemes (blueprint
`prop-trf-trace-class-unconditional`). -/
noncomputable def traceClass (F : c.FixedLocus) : BorelMooreSection ℓ F.F :=
  (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ F.ι)).hom ≫
    ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ F.ι).homEquiv _ _).symm
      (c.mate ≫ c.traceMap F)

/-- **The trace class is unconditionally defined** (blueprint
`prop-trf-trace-class-unconditional`): it is the image of the mate of `u` under the
`ℚ̄_ℓ`-linear map `Hom(ℚ̄_ℓ,C, 𝓗_c(K)) ⟶ Hom(ℚ̄_ℓ,Fix(c), ω_Fix(c))` induced by the trace
morphism, defined for every coefficient map `u`. -/
lemma traceClass_eq (F : c.FixedLocus) :
    c.traceClass F = (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ F.ι)).hom ≫
      ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ F.ι).homEquiv _ _).symm
        (c.mateEquiv c.u ≫ c.traceMap F) :=
  rfl

end

end Correspondence

namespace Correspondence

variable [QuasiCompact X.hom] [IsProper X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)


/-- **The Lefschetz–Verdier formula** (blueprint `thm-trf-fixed-point-localization`,
`sk-c-proper-global`): for `X` proper over `s`, an endocorrespondence `c` with proper ordinary
leg `c₂` and proper fixed locus,
the trace of the global operator is the integral of the trace class,
`tr(T_c(u) | RΓ_c(X, K)) = ∫_Fix(c) Tr_c(u)`. -/
theorem trace_globalOperator_eq_integral_traceClass [IsProper c.c₂.left]
    (F : c.FixedLocus) [IsProper F.F.hom]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj K)] :
    trace c.globalOperator = (c.traceClass F).integral :=
  sorry

/-- **The Lefschetz–Verdier trace comparison** (blueprint `thm-trf-lefschetz-verdier`): for `X`
proper over `s`, an endocorrespondence with proper ordinary leg and a fixed locus which is the
disjoint union of finitely many open and closed subschemes `j_β : B_β ⟶ Fix(c)` proper over `s`,
the trace of the global operator is the sum of the local terms,
`tr(T_c(u) | RΓ_c(X, K)) = ∑_β LT_β(u)`. It is the fixed-point localization
`trace_globalOperator_eq_integral_traceClass` followed by the decomposition of the integral
into local terms (`BorelMooreSection.integral_eq_sum_localTerm`). -/
theorem trace_globalOperator_eq_sum_localTerm [IsProper c.c₂.left]
    (F : c.FixedLocus) [IsProper F.F.hom]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj K)]
    {ι : Type*} [Fintype ι] (B : ι → Over (Spec (.of k))) [∀ i, QuasiCompact (B i).hom]
    [∀ i, IsProper (B i).hom] (j : ∀ i, B i ⟶ F.F) [∀ i, IsOpenImmersion (j i).left]
    [∀ i, IsClosedImmersion (j i).left]
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (j i).left.base)
      (Set.range (j i').left.base))
    (hcover : ⋃ i, Set.range (j i).left.base = Set.univ) :
    trace c.globalOperator = ∑ i, (c.traceClass F).localTerm (j i) := by
  rw [c.trace_globalOperator_eq_integral_traceClass F,
    BorelMooreSection.integral_eq_sum_localTerm B j hdisj hcover]

instance (v : K ⟶ K) : IsProper (fixedLocusOfEnd v).F.hom :=
  inferInstanceAs (IsProper X.hom)


/-- **Point normalization of the pairing** (blueprint `prop-trf-pairing-point-normalization`):
over the base point, the trace class of the diagonal correspondence of an endomorphism `v` of
a perfect complex integrates to the categorical trace of `v`, `∫_s Tr(v) = tr(v)`. -/
theorem integral_traceClass_ofEnd {K : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    [HasRightDual K] (v : K ⟶ K) :
    ((ofEnd K v).traceClass (fixedLocusOfEnd v)).integral = trace v :=
  sorry

end Correspondence

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace WeilBoundedConstructible

variable {Φ : X ⟶ X}


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
