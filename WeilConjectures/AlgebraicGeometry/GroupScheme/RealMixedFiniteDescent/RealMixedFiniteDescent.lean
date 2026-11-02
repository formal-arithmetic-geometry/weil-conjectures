/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPullback.NativeCondensedPullbackFrobenius
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite constant-extension descent for mixed native condensed Weil modules

Source: latest blueprint, part-weights-riemann-hypothesis/sec-deligne-laumon-general/
sec-real-sheaves-on-an-arbitrary-base/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md, paragraph 5
(blueprint: lem-zl-real-mixed-finite-descent).

The whole extension is regarded over k0. The index-one native presentation is
base change along the isomorphism k0 to its degree-one subfield. It retains all
m geometric sheets and q-Frobenius.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.RealMixedFiniteDescent
open NativeL2

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)

/-- The finite extension spectrum map, using the native finite-field datum.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
def fieldMap : Spec (.of (NativeCondensedPullback.constantExtensionDatum D m hm).k₀) ⟶
    Spec (.of D.k₀) := Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))

/-- Finiteness of the extension spectrum map follows from finiteness of its field.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
instance fieldMap_finite : IsFinite (fieldMap D m hm) := by
  let := (D.extensionEmbedding m hm).toAlgebra
  have := (NativeCondensedPullback.constantExtensionField_properties D m hm).1
  exact (IsFinite.SpecMap_iff _).mpr
    (show Module.Finite D.k₀ (D.extensionSubfield m hm) from inferInstance)

variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- The whole finite constant extension regarded over the original finite field.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
def originalModel : Over (Spec (.of D.k₀)) :=
  Over.mk (pullback.snd X₀.hom (fieldMap D m hm) ≫ fieldMap D m hm)

/-- The canonical degree-m projection g0.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
def originalProjection : originalModel D m hm X₀ ⟶ X₀ :=
  Over.homMk (pullback.fst X₀.hom (fieldMap D m hm)) pullback.condition

/-- Finite type of the restricted extension.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
instance originalModel_lft : LocallyOfFiniteType (originalModel D m hm X₀).hom := by
  change LocallyOfFiniteType (pullback.snd X₀.hom (fieldMap D m hm) ≫ fieldMap D m hm)
  infer_instance

/-- Quasi-compactness of the restricted extension.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
instance originalModel_qc : QuasiCompact (originalModel D m hm X₀).hom := by
  change QuasiCompact (pullback.snd X₀.hom (fieldMap D m hm) ≫ fieldMap D m hm)
  infer_instance

/-- Separatedness of the restricted extension.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
instance originalModel_separated : IsSeparated (originalModel D m hm X₀).hom := by
  change IsSeparated (pullback.snd X₀.hom (fieldMap D m hm) ≫ fieldMap D m hm)
  infer_instance

/-- The same scheme in the index-one presentation required by the native API.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
def model : Over (Spec (.of (NativeCondensedPullback.constantExtensionDatum D 1
    (by omega)).k₀)) :=
  (Over.pullback (fieldMap D 1 (by omega))).obj (originalModel D m hm X₀)

/-- Finite type in the index-one presentation.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
instance model_lft : LocallyOfFiniteType (model D m hm X₀).hom := by
  change LocallyOfFiniteType (pullback.snd (originalModel D m hm X₀).hom _)
  infer_instance

/-- Quasi-compactness in the index-one presentation.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
instance model_qc : QuasiCompact (model D m hm X₀).hom := by
  change QuasiCompact (pullback.snd (originalModel D m hm X₀).hom _)
  infer_instance

/-- Separatedness in the index-one presentation.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
instance model_separated : IsSeparated (model D m hm X₀).hom := by
  change IsSeparated (pullback.snd (originalModel D m hm X₀).hom _)
  infer_instance

/-- The canonical f0 in the native API; its geometric map has all m sheets.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
def projection : Over.mk ((model D m hm X₀).hom ≫ fieldMap D 1 (by omega)) ⟶ X₀ :=
  Over.homMk (pullback.fst (originalModel D m hm X₀).hom (fieldMap D 1 (by omega)) ≫
    (originalProjection D m hm X₀).left)
    (by simp only [Category.assoc, Over.w]; exact pullback.condition)

/-- The actual geometric projection of degree m in the native presentation.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
def geometricMap :=
  NativeCondensedPullback.geometricMap D 1 (by omega) X₀ (model D m hm X₀)
    (projection D m hm X₀)

variable (l : ℕ) [Fact l.Prime]

/-- The canonical native pullback, with index one to retain the original q-Frobenius.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
@[irreducible] def pullback :=
  NativeCondensedPullback.functor D 1 (by omega) X₀ (model D m hm X₀)
    (projection D m hm X₀) l

/-- The actual lower-star direct image, with Weil structure from Frobenius exchange.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
@[irreducible] def directImage :
    WeilModule (NativeCondensedPullback.constantExtensionDatum D 1 (by omega)) l
      (model D m hm X₀) ⥤ WeilModule D l X₀ :=
  IsoAlgebra.mapOfNatIso
    (asIso (CondensedRing.lowerStarBaseChange (Profinite.padicAlgClRingObj l)
      (NativeCondensedPullback.geometricMap_frobenius D 1 (by omega) X₀
        (model D m hm X₀) (projection D m hm X₀))))

/-- The canonical native pullback has exactly the ordinary upper-star carrier.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent).
Proof: unfold the wrapper pullback and apply NativeCondensedPullback.carrier_eq. -/
theorem pullback_carrier (M : WeilModule D l X₀) :
    ((pullback D m hm X₀ l).obj M).carrier =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (geometricMap D m hm X₀)).obj M.carrier := by
  sorry

/-- The direct-image carrier is exactly the ordinary lower-star carrier.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent).
Proof: unfold directImage and the object action of IsoAlgebra.mapOfNatIso. The
transport changes the Weil structure only, leaving the lower-star carrier. -/
theorem directImage_carrier
    (N : WeilModule (NativeCondensedPullback.constantExtensionDatum D 1 (by omega)) l
      (model D m hm X₀)) :
    ((directImage D m hm X₀ l).obj N).carrier =
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
        (geometricMap D m hm X₀)).obj N.carrier := by
  sorry

/-- The ordinary adjunction unit, transported through the two carrier equalities.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
@[irreducible] def unitCarrier (M : WeilModule D l X₀) :
    M.carrier ⟶ ((directImage D m hm X₀ l).obj ((pullback D m hm X₀ l).obj M)).carrier :=
  (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
    (geometricMap D m hm X₀)).unit.app M.carrier ≫
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
      (geometricMap D m hm X₀)).map (eqToHom (pullback_carrier D m hm X₀ l M).symm) ≫
    eqToHom (directImage_carrier D m hm X₀ l ((pullback D m hm X₀ l).obj M)).symm

/-- The ordinary adjunction unit is Weil-equivariant.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent).
Proof: lowerStarBaseChange is the mate of upperStarSquareComparison. The mate-unit
identity and naturality give the Weil square for the native index-one pullback,
after identifying its carrier and the direct-image carrier by the two lemmas above. -/
theorem unit_equivariance (M : WeilModule D l X₀) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom).map (unitCarrier D m hm X₀ l M) ≫
      ((directImage D m hm X₀ l).obj ((pullback D m hm X₀ l).obj M)).str.hom =
    M.str.hom ≫ unitCarrier D m hm X₀ l M := by
  sorry

/-- The actual adjunction unit as a Weil morphism, with its specified carrier map.
Source: latest blueprint, paragraph 5 (blueprint: lem-zl-real-mixed-finite-descent). -/
@[irreducible] def unit (M : WeilModule D l X₀) :
    M ⟶ (directImage D m hm X₀ l).obj ((pullback D m hm X₀ l).obj M) :=
  ObjectProperty.homMk
    { f := unitCarrier D m hm X₀ l M
      h := unit_equivariance D m hm X₀ l M }

end WeilConjectures.RealMixedFiniteDescent

namespace WeilConjectures
open NativeL2 RealMixedFiniteDescent

/-- Exact finite direct image, weight preservation, canonical trace and mixed descent.
Source: latest blueprint, part-weights-riemann-hypothesis/sec-deligne-laumon-general/
sec-real-sheaves-on-an-arbitrary-base/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md, paragraph 5
(blueprint: lem-zl-real-mixed-finite-descent).

Proof plan, following the seven steps of the node:
1. The degree-m finite field extension is separable. Its spectrum map, its base
   changes, and the index-one presentation are finite etale; a field basis gives
   degree m. Noetherianity makes the geometric projection finitely presented.
2. Apply lem-fd-proetale-finite-pushforward-exact and
   lem-a1-condensed-finite-etale-stalk-cycles to the actual lower-star carrier.
   Exactness in the Weil heart is detected on carriers, by the exact
   coefficient heart and lem-zl-cyclic-return-exact-equivalence at index one.
   Apply lem-a1-finite-map-purity to each pure quotient. Pullback is the native
   index-one functor of lem-zl-condensed-pullback-frobenius.
3. Apply exact direct image to each short exact sequence of a finite filtration.
   Its quotients are the direct images of the old quotients and have the same
   weights; zero quotients and repeated terms are allowed.
4. On a weakly etale splitting chart use the product comparison of
   lem-weil-pbc-split-proetale-module-product-map. Sum the counit projections.
   The sheet-sum compatibility and split-Hom descent lemmas glue these sums;
   separatedness of the target sheaf proves uniqueness.
5. Frobenius permutes the sheets. Summation is permutation invariant and
   commutes with the Weil structure, so the glued trace is Weil-equivariant.
   The adjunction triangle identity makes the actual unit diagonal; therefore
   its composite with the sum is m times the identity on each chart and globally.
6. The constant scalar 1/m belongs already to Q_l in the condensed coefficient
   ring. Multiply the trace by it, obtaining rho with m rho = Tr and eta rho = id,
   even when l divides m.
7. Exact image carries a pure filtration of the pullback to a mixed filtration.
   The retraction and lem-a1-mixed-direct-summand descend mixedness with the same
   weight bound. The empty filtration, zero modules and empty schemes are included.
-/
theorem real_mixed_finite_descent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) (iota : PadicAlgCl l →+* ℂ) :
    PreservesFiniteLimits (directImage D m hm X₀ l) ∧
    PreservesFiniteColimits (directImage D m hm X₀ l) ∧
    (∀ N : WeilModule (NativeCondensedPullback.constantExtensionDatum D 1 (by omega)) l
        (model D m hm X₀),
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        ((NativeCondensedPullback.constantExtensionDatum D 1 (by omega)).geometricFiber
          (model D m hm X₀)).left N.carrier →
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber X₀).left ((directImage D m hm X₀ l).obj N).carrier) ∧
    (∀ (N : WeilModule (NativeCondensedPullback.constantExtensionDatum D 1 (by omega)) l
        (model D m hm X₀)) (w : ℝ),
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        ((NativeCondensedPullback.constantExtensionDatum D 1 (by omega)).geometricFiber
          (model D m hm X₀)).left N.carrier →
      NativeL2.Pure (NativeCondensedPullback.constantExtensionDatum D 1 (by omega)) l
        (model D m hm X₀) N iota w →
      NativeL2.Pure D l X₀ ((directImage D m hm X₀ l).obj N) iota w) ∧
    (∀ (n : ℕ)
      (G : Fin (n + 1) →
        WeilModule (NativeCondensedPullback.constantExtensionDatum D 1 (by omega)) l
          (model D m hm X₀))
      (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ) (v : Fin n → ℝ),
      IsZero (G 0) → (∀ i, Mono (φ i)) →
      (∀ i, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        ((NativeCondensedPullback.constantExtensionDatum D 1 (by omega)).geometricFiber
          (model D m hm X₀)).left (G i).carrier) →
      (∀ i, NativeL2.Pure (NativeCondensedPullback.constantExtensionDatum D 1 (by omega)) l
        (model D m hm X₀) (cokernel (φ i)) iota (v i)) →
      ∀ i, NativeL2.Pure D l X₀ (cokernel ((directImage D m hm X₀ l).map (φ i)))
        iota (v i)) ∧
    (∀ (N : WeilModule (NativeCondensedPullback.constantExtensionDatum D 1 (by omega)) l
        (model D m hm X₀)) (w : ℝ),
      NativeL2.Mixed (NativeCondensedPullback.constantExtensionDatum D 1 (by omega)) l
        (model D m hm X₀) N iota w →
      NativeL2.Mixed D l X₀ ((directImage D m hm X₀ l).obj N) iota w) ∧
    (∀ M : WeilModule D l X₀,
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber X₀).left M.carrier →
      ∃ (Tr ρ : (directImage D m hm X₀ l).obj ((pullback D m hm X₀ l).obj M) ⟶ M),
        RealMixedFiniteDescent.unit D m hm X₀ l M ≫ Tr = m • 𝟙 M ∧
        RealMixedFiniteDescent.unit D m hm X₀ l M ≫ ρ = 𝟙 M ∧ m • ρ = Tr) ∧
    (∀ (M : WeilModule D l X₀) (w : ℝ),
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber X₀).left M.carrier →
      NativeL2.Mixed (NativeCondensedPullback.constantExtensionDatum D 1 (by omega)) l
        (model D m hm X₀) ((pullback D m hm X₀ l).obj M) iota w →
      NativeL2.Mixed D l X₀ M iota w) := by
  sorry

end WeilConjectures
