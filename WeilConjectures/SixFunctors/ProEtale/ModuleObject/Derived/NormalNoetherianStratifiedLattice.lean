/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.StratifiedLattice
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalStratifiedLatticeData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.SpectralEtaleLocalLattices
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.SpectralFiniteEtaleTraceLattice

/-! # Integral lattices on finite strata of normal Noetherian schemes.

Source: blueprint `sk-lem-stratified-lattice`, extended as directed by
Wei Yang, Zulip #1412, answer 17 (2026-11-01), for clause (4) of
`thm-lisse-qlbar-representations`. This keeps the original finite-type theorem
and supplies the normal-Noetherian instance required by its dense-open argument.
(blueprint: sk-lem-stratified-lattice).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Pullback of a scalar-extension comparison around a cartesian square. -/
theorem nonempty_extendScalars_pullback_iso
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a]
    (X U Y : Scheme.{u}) (f : U ⟶ X) (j : Y ⟶ X)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U))
    (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar B f).obj L) :
    Nonempty ((Mod.extendScalars (coefficientMap a (pullback f j))).obj
        ((upperStar A (pullback.fst f j)).obj M) ≅
      (upperStar B (pullback.snd f j)).obj ((upperStar B j).obj L)) :=
  ⟨(pullIso a (pullback.fst f j)).app M ≪≫
    (upperStar B (pullback.fst f j)).mapIso e ≪≫
    (upperStarComp B (pullback.fst f j) f).symm.app L ≪≫
    eqToIso (congrArg (fun g ↦ (upperStar B g).obj L) (pullback.condition (f := f) (g := j))) ≪≫
    (upperStarComp B (pullback.snd f j) j).app L⟩

/-- A property of morphisms into a qcqs scheme which holds whenever the base change of a
fixed qcqs etale cover is finite etale holds on the strata of a finite stratification. -/
theorem exists_stratification_of_etale_cover
    (X U : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] (f : U ⟶ X) [Etale f]
    (Q : ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop)
    (hQ : ∀ (Y : Scheme.{u}) (j : Y ⟶ X),
      IsFinite (pullback.snd f j) → Etale (pullback.snd f j) → Q Y j) :
    ∃ S : Scheme.FiniteLocallyClosedStratification X, ∀ i, Q (S.domain i) (S.immersion i) := by
  obtain ⟨S, _, hS⟩ := Scheme.exists_etale_stratified_finite f
  exact ⟨{ n := S.n
           stratum := S.stratum
           isLocallyClosed_stratum := S.isLocallyClosed_stratum
           iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
           pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
           domain := S.domain
           immersion := S.immersion
           isImmersion := S.isImmersion
           range_immersion := S.range_immersion },
    fun i ↦ hQ (S.domain i) (S.immersion i) (hS i).1 (hS i).2⟩

/-- Assemble coefficient lattices on the strata of a qcqs scheme from an etale-local
lattice and descent of lattices along finite etale surjections.
(blueprint: sk-lem-stratified-lattice). -/
theorem exists_stratified_coefficient_lattice
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (hL : LocallyFree (condensedRingObj B X) L)
    (hlocal : ∃ (U : Scheme.{u}) (f : U ⟶ X), Etale f ∧ Surjective f ∧
      CompactSpace U ∧ QuasiSeparatedSpace U ∧
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U),
      LocallyFree (condensedRingObj A U) M ∧
      Nonempty ((Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar B f).obj L))
    (descend : ∀ (Y V : Scheme.{u}) (q : V ⟶ Y) [IsFinite q] [Etale q] [Surjective q]
      (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj B Y)),
      LocallyFree (condensedRingObj B Y) P →
      ∀ N : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj A V),
      LocallyFree (condensedRingObj A V) N →
      Nonempty ((Mod.extendScalars (coefficientMap a V)).obj N ≅ (upperStar B q).obj P) →
      ∃ N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y),
        LocallyFree (condensedRingObj A Y) N ∧
        ∃ ι : N ⟶ (Mod.comap (coefficientMap a Y)).obj P,
          Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
            (coefficientMap a Y)).homEquiv N P).symm ι)) :
    ∃ S : Scheme.FiniteLocallyClosedStratification X, ∀ i,
      ∃ N : Mod (Sheaf (Scheme.ProEt.topology (S.domain i)) Ab.{u + 1})
          (condensedRingObj A (S.domain i)),
        LocallyFree (condensedRingObj A (S.domain i)) N ∧
        ∃ ι : N ⟶ (Mod.comap (coefficientMap a (S.domain i))).obj
            ((upperStar B (S.immersion i)).obj L),
          Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
            (coefficientMap a (S.domain i))).homEquiv N
              ((upperStar B (S.immersion i)).obj L)).symm ι) := by
  obtain ⟨U, f, hf, hs, hc, hq, M, hM, ⟨e⟩⟩ := hlocal
  apply exists_stratification_of_etale_cover X U f
    (fun Y j ↦ ∃ N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y),
      LocallyFree (condensedRingObj A Y) N ∧
      ∃ ι : N ⟶ (Mod.comap (coefficientMap a Y)).obj ((upperStar B j).obj L),
        Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
          (coefficientMap a Y)).homEquiv N ((upperStar B j).obj L)).symm ι))
  intro Y j _ _
  exact descend Y (pullback f j) (pullback.snd f j) ((upperStar B j).obj L)
    (locallyFree_upperStar B j hL) ((upperStar A (pullback.fst f j)).obj M)
    (locallyFree_upperStar A (pullback.fst f j) hM)
    (nonempty_extendScalars_pullback_iso A B a X U Y f j L M e)

/-- A lisse rational module on a scheme with Noetherian underlying space admits an embedded
lisse integral lattice on each stratum of a finite locally closed stratification.
This is the argument of `exists_stratified_lisse_integral_lattice`, whose finite-type
hypotheses are used only to obtain a Noetherian underlying space.
(blueprint: sk-lem-stratified-lattice). -/
theorem exists_stratified_lisse_integral_lattice_of_noetherianSpace
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let A := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers l E)
    let B := Profinite.continuousMapRingObj.{u} E
    let a : A ⟶ B :=
      (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap
            (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)
    ∀ L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X),
      LocallyFree (condensedRingObj B X) L →
      ∃ S : Scheme.FiniteLocallyClosedStratification X, ∀ i : Fin S.n,
        let T := S.domain i
        let aT := (upperStarFromPoint T).map a
        let LT := (CondensedRing.upperStar B (S.immersion i)).obj L
        ∃ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj A T),
          LocallyFree (condensedRingObj A T) M ∧
          ∃ ι : M ⟶ (Mod.comap aT).obj LT,
            Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction aT).homEquiv M LT).symm ι) := by
  dsimp only
  intro L hL
  apply exists_stratified_coefficient_lattice _ _ _ X L hL (spectralLisse_etale_lattice l E X L hL)
  intro Y V q _ _ _ P hP N hN he
  obtain ⟨e⟩ := he
  exact spectralFiniteEtaleTrace_lattice l E Y P hP q N hN e

/-- A lisse rational module on a normal Noetherian scheme admits an embedded
lisse integral lattice on each stratum of a finite locally closed stratification.
There is no base field, characteristic restriction, separatedness assumption,
connectedness assumption, or assumption that `l` is invertible on the scheme.

Source: blueprint `sk-lem-stratified-lattice`, sheaf of lattices and trace proof;
Wei Yang #1412, answer 17, normal-Noetherian extension; Stacks 07RY and 07RZ.

Proof. The scheme has Noetherian underlying space and is qcqs. Split into the
finitely many locally constant rank pieces. The qcqs lattice-scheme theorem
represents lattices by a separated surjective etale scheme with its universal
lattice. Choose finitely many affine opens with images covering the base; their
disjoint union is a qcqs separated etale surjection. Stacks 07RY and 07RZ give a
finite locally closed stratification on which this cover is finite etale. Pull
back the universal lattice and its scalar-extension comparison to each cover.
The image under the sheet-sum trace is a locally free integral lattice on the
stratum: on splitting charts it is a finite sum of lattices. Exact scalar
extension and naturality of the localization counit show that the adjoint of
this actual inclusion is an isomorphism. These are precisely the atlas,
stratification and trace steps of exists_topologicalStratifiedLatticeData,
with the spectral norm and its valuation subring. No cover degree is inverted.
Normality is retained here for the expert-requested specialization, although
the construction itself only needs a Noetherian underlying space. Empty schemes,
zero rank, varying ranks, and residue characteristic `l` are included.
(blueprint: sk-lem-stratified-lattice).
-/
theorem exists_stratified_lisse_integral_lattice_of_normal
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (_hnormal : ∀ z : X, IsDomain (X.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.presheaf.stalk z)) :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let A := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers l E)
    let B := Profinite.continuousMapRingObj.{u} E
    let a : A ⟶ B :=
      (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap
            (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)
    ∀ L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X),
      LocallyFree (condensedRingObj B X) L →
      ∃ S : Scheme.FiniteLocallyClosedStratification X, ∀ i : Fin S.n,
        let T := S.domain i
        let aT := (upperStarFromPoint T).map a
        let LT := (CondensedRing.upperStar B (S.immersion i)).obj L
        ∃ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj A T),
          LocallyFree (condensedRingObj A T) M ∧
          ∃ ι : M ⟶ (Mod.comap aT).obj LT,
            Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction aT).homEquiv M LT).symm ι) := by
  have : IsNoetherian X := ⟨⟩
  exact exists_stratified_lisse_integral_lattice_of_noetherianSpace l E X

end AlgebraicGeometry.ProEtale.CondensedRing
