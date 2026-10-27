/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions
import Sheaf.Paper.FiniteFreeScalarProjection
import Sheaf.Paper.ScalarExchangeConstituents
import Sheaf.Paper.FiniteFreeCompactScalar

/-!
# Finite-free scalar extension of the specified projection and exchange maps

Source: blueprint main-20261015, sk-thm-purity-transport, proof Steps 1 and 3;
Stacks 07A4, 0E47, 0GL1, 03S6, 0F7I and 0GL6
(blueprint: lem-pur-finite-free-projection-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
open WeilConjectures.FiniteFreeCoefficients
namespace WeilConjectures.FiniteFreeProjectionExchange

attribute [local irreducible] Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  Functor.mapDerivedCategory Etale.lowerStar Etale.upperStar
  Functor.leftAdjoint Functor.rightAdjoint
  ProEtale.pbcFixedScalarExtension ProEtale.lowerStar
  ProEtale.finiteCoefficientChangeDirectImageMap Etale.finiteCoefficientDirectImageMap
private theorem direct_naturality (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Sites.D pro A X} (r : M ⟶ N) :
    (Sites.scalar pro φ Y).map ((Sites.push pro A f).map r) ≫ Sites.direct pro φ f N =
      Sites.direct pro φ f M ≫
        (Sites.push pro B f).map ((Sites.scalar pro φ X).map r) := by
  cases pro <;> dsimp only [Sites.direct, Sites.scalar, Sites.push]
  · exact Etale.finiteCoefficientDirectImageMap_naturality φ f r
  · exact ProEtale.finiteCoefficientDirectImageMap_naturality
      (T := X) (X := Y) (K := M) (L := N) φ f r

private theorem comparison_naturality (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {M N : Sites.D pro A X} (r : M ⟶ N) :
    (Sites.scalar pro φ Y).map ((support pro A c).map r) ≫ comparison pro φ c N =
      comparison pro φ c M ≫
        (support pro B c).map ((Sites.scalar pro φ X).map r) := by
  dsimp only [comparison, support, Functor.comp_map]
  rw [← Category.assoc, direct_naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun s ↦ Sites.direct pro φ c.g ((openExtension pro A c.i).obj M) ≫
    (Sites.push pro B c.g).map s) ((scalarOpen pro φ c.i).hom.naturality r)

private theorem exchange_factorization (pro : Bool) (A : Type (u + 1))
    [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback a b f g) (c : Compactification f)
    (M : Sites.D pro A X) :
    exchange pro A sq c M =
      properExchange pro A (IsPullback.of_hasPullback c.g g)
          ((openExtension pro A c.i).obj M) ≫
        (Sites.push pro A (c.ofIsPullback sq).g).map
          (openExchange pro A (c.isPullback_i_ofIsPullback sq) M) := by
  cases pro <;>
    simp only [exchange, properExchange, openExtension, openExchange, Sites.push,
      Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap,
      ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap,
      ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeIso,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Iso.trans_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_inv, Functor.map_comp, Category.assoc, id_eq, Iso.symm_inv]

set_option backward.isDefEq.respectTransparency false in
private theorem properExchange_naturality (pro : Bool) (A : Type (u + 1)) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback a b f g)
    {M N : Sites.D pro A X} (r : M ⟶ N) :
    (pull pro A g).map ((Sites.push pro A f).map r) ≫
        properExchange pro A sq N =
      properExchange pro A sq M ≫ (Sites.push pro A b).map ((pull pro A a).map r) := by
  cases pro <;> dsimp only [pull, Sites.push, properExchange]
  · exact (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).naturality r
  · exact (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).naturality r


private theorem exchange_pasting (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback a b f g) (c : Compactification f)
    (M : Sites.D pro A X)
    (hp : ProperExchangeEquation pro φ (IsPullback.of_hasPullback c.g g)
      ((openExtension pro A c.i).obj M))
    (ho : OpenExchangeEquation pro φ (c.isPullback_i_ofIsPullback sq) M) :
    ExchangeEquation pro φ sq c M := by
  have hnat := direct_naturality pro φ (c.ofIsPullback sq).g
    (openExchange pro A (c.isPullback_i_ofIsPullback sq) M)
  have hp' :
      (Sites.scalar pro φ Y').map
          (properExchange pro A (IsPullback.of_hasPullback c.g g)
            ((openExtension pro A c.i).obj M)) ≫
        Sites.direct pro φ (c.ofIsPullback sq).g
          ((pull pro A (pullback.fst c.g g)).obj ((openExtension pro A c.i).obj M)) =
      (scalarPull pro φ g).inv.app
          ((Sites.push pro A c.g).obj ((openExtension pro A c.i).obj M)) ≫
        (pull pro B g).map (Sites.direct pro φ c.g ((openExtension pro A c.i).obj M)) ≫
        properExchange pro B (IsPullback.of_hasPullback c.g g)
          ((Sites.scalar pro φ c.Z).obj ((openExtension pro A c.i).obj M)) ≫
        (Sites.push pro B (c.ofIsPullback sq).g).map
          ((scalarPull pro φ (pullback.fst c.g g)).hom.app
            ((openExtension pro A c.i).obj M)) := hp
  dsimp only [ExchangeEquation, comparison, support, Functor.comp_map, Functor.comp_obj]
  rw [exchange_factorization, exchange_factorization]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat]
  try simp only [Category.assoc]
  erw [reassoc_of% hp']
  dsimp only [OpenExchangeEquation] at ho
  simp only [← Functor.map_comp]
  rw [ho]
  simp only [Functor.map_comp]
  simp only [← Functor.map_comp, Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp]
  erw [← reassoc_of% (properExchange_naturality pro B
    (IsPullback.of_hasPullback c.g g) ((scalarOpen pro φ c.i).hom.app M))]


attribute [local irreducible] Sites.scalar Sites.push Sites.direct Sites.tensor
  pull openExtension scalarPull scalarOpen comparison support tensorPullTarget

/-- Finite-free coefficient extension preserves the specified compact-support projection
and exchange, the individual proper and open constituents, and every proper refinement.
The tensor comparison is required to be the normalized ordinary balancing map, and no
smooth orientation or trace data are parameters.

Source: blueprint main-20261015, sk-thm-purity-transport, proof Steps 1 and 3;
Stacks 07A4, 0E47, 0GL1, 03S6, 0F7I and 0GL6
(blueprint: lem-pur-finite-free-projection-exchange).

Proof plan, following the ten steps of the DAG node:
1. Finite-free extension is exact and preserves constructibility and Tor intervals.
Pullback, open extension and direct image preserve the indicated finite-Tor domains
by lem-sf-flat-model, lem-trf-open-ctf and the two direct-image closure results.
2. The proper counit-transpose comparison is lem-coef-finite-direct-image; the open
comparison is lem-coef-etale-open-tensor or lem-sf-open-tensor-normalization.
Their composite is comparison, hence is invertible and natural.
3. Compute scalar/pullback and tensor comparisons on K-flat representatives using
lem-pc-kflat-resolution and lem-pur-derived-change-of-rings. Both routes send a pure
tensor to its inverse image with the same coefficient. Balanced multiplication proves
coherence, including identities, compositions and inverse-image square identifications.
4. The direct-image map is the mate of this scalar/pullback comparison. Its counit
identity and triangle identities give its unit identity. Mate pasting gives its cocycle.
5. Take the open adjoint of the scalar/open projection square. Both sides become the
same balanced reassociation, by the unit normalizations of the open tensor maps.
6. The open base-change inverse is the adjunct of the pulled-back open unit, by
lem-cbc-extension-zero-base-change and cor-cbc-derived-extension-zero-base-change.
After taking adjuncts the scalar square is Step 3 and the open unit equation. On the
pro-etale site use lem-fix-open-scalar-exchange with these same maps.
7. Proper exchange is the mate of the inverse-image square. The coefficient cube of
left-adjoint comparisons commutes by Step 3. Mate pasting gives ProperExchangeEquation
on each site, with the actual proper exchange rather than an unspecified isomorphism.
8. Apply lem-sf-pf-coefficient-realization-transport on each closed finite-Tor domain,
using Steps 1--7. Its compactification composites are the present projection and
exchange by lem-weil-finite-compact-projection-formula and def-cbc-exchange-map.
9. For an etale proper refinement use lem-sf-proper-open-coefficient-refinement and
the direct-image composition equation. By lem-amb-etale-compact-comparisons these
are the coherent canonical comparisons of all compactifications.
10. Choose any etale-origin witness by lem-sf-proetale-constructible-origin. The
coefficient/site/open cube commutes by lem-sf-open-comparison-unit-normalization;
the proper cube commutes by the canonical mate and mate pasting. Transport Step 9
using lem-sf-proper-open-comparison-site-normalization. Naturality gives the asserted
refinement square for every witness and every isomorphic constructible input. -/
theorem finite_free_projection_exchange (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (t : FiniteCoefficientAdjoints.Stage l E) :
    ∀ pro : Bool, ∃ μ : TensorFamily pro (extensionArrow t).ringMap,
    ∀ (X Y : Scheme.{u})
      [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
      [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f],
    (∀ (c : Compactification f)
      (M : Sites.D pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X),
      Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X M →
      IsIso (comparison pro (extensionArrow t).ringMap c M)) ∧
    (∀ (c : Compactification f)
      (M N : Sites.D pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X)
      (_hM : Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X M)
      (_hN : Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X N)
      (r : M ⟶ N),
      (Sites.scalar pro (extensionArrow t).ringMap Y).map
          ((support pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring c).map r) ≫
          comparison pro (extensionArrow t).ringMap c N =
        comparison pro (extensionArrow t).ringMap c M ≫
          (support pro t.ring c).map ((Sites.scalar pro (extensionArrow t).ringMap X).map r)) ∧
    (∀ (c d : Compactification f)
      (M : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (FiniteCoefficientAdjoints.baseStage t.exponent).ring)))
      (N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} t.ring)))
      (e : (origin pro t.ring X).obj N ≅
        (Sites.scalar pro (extensionArrow t).ringMap X).obj
          ((origin pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X).obj M)),
      Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X
          ((origin pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X).obj M) →
      RefinementEquation pro (extensionArrow t).ringMap c d M N e) ∧
    (∀ (c : Compactification f)
      (M : Sites.D pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X)
      (K : Sites.D pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring Y),
      Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X M →
      Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring Y K →
      ProjectionEquation pro (extensionArrow t).ringMap μ c M K) ∧
    (∀ (M : Sites.D pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X)
      (K : Sites.D pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring Y),
      Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X M →
      Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring Y K →
      (IsProper f → ProperProjectionEquation pro (extensionArrow t).ringMap μ f M K) ∧
      (∀ [IsOpenImmersion f],
        OpenProjectionEquation pro (extensionArrow t).ringMap μ f M K)) ∧
    (∀ (X' Y' : Scheme.{u})
      [X'.Over (Spec (.of D.k))] [Y'.Over (Spec (.of D.k))]
      [IsSeparated (X' ↘ Spec (.of D.k))] [IsSeparated (Y' ↘ Spec (.of D.k))]
      [LocallyOfFiniteType (X' ↘ Spec (.of D.k))] [QuasiCompact (X' ↘ Spec (.of D.k))]
      [LocallyOfFiniteType (Y' ↘ Spec (.of D.k))] [QuasiCompact (Y' ↘ Spec (.of D.k))]
      (a : X' ⟶ X) (b : X' ⟶ Y') (g : Y' ⟶ Y)
      [a.IsOver (Spec (.of D.k))] [b.IsOver (Spec (.of D.k))]
      [g.IsOver (Spec (.of D.k))] (sq : IsPullback a b f g)
      (M : Sites.D pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X),
      Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X M →
      (∀ c : Compactification f, ExchangeEquation pro (extensionArrow t).ringMap sq c M) ∧
      (IsProper f → ProperExchangeEquation pro (extensionArrow t).ringMap sq M) ∧
      (∀ [IsOpenImmersion f] [IsOpenImmersion b],
        OpenExchangeEquation pro (extensionArrow t).ringMap sq M)) := by
  have hf := (finite_free_coefficient_extension D l _hl E).2.1
    (FiniteCoefficientAdjoints.baseStage t.exponent) t (extensionArrow t) rfl
  intro pro
  obtain ⟨μ, hproper, hopen, hcompact⟩ :=
    finite_free_scalar_projection (extensionArrow t).ringMap hf pro
  refine ⟨μ, ?_⟩
  intro X Y _ _ _ _ _ _ _ _ f _ _ _ _
  have hc := finite_free_compact_scalar (extensionArrow t).ringMap hf pro (f := f)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c M _
    exact hc.1 c M
  · intro c M N _ _ r
    exact comparison_naturality pro (extensionArrow t).ringMap c r
  · intro c d M N e _
    exact hc.2 c d M N e
  · intro c M K _ _
    exact hcompact c M K
  · intro M K _ _
    constructor
    · intro _
      exact hproper f M K
    · intro _
      exact hopen f M K
  · intro X' Y' _ _ _ _ _ _ _ _ a b g _ _ _ sq M _
    have he := scalar_exchange_constituents (extensionArrow t).ringMap pro sq M
    refine ⟨?_, fun _ ↦ he.1, he.2⟩
    intro c
    apply exchange_pasting pro (extensionArrow t).ringMap sq c M
    · exact (scalar_exchange_constituents (extensionArrow t).ringMap pro
        (IsPullback.of_hasPullback c.g g) ((openExtension pro _ c.i).obj M)).1
    · exact (scalar_exchange_constituents (extensionArrow t).ringMap pro
        (c.isPullback_i_ofIsPullback sq) M).2

end WeilConjectures.FiniteFreeProjectionExchange
