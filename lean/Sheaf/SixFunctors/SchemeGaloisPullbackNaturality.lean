/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback

/-!
# Pullback naturality of the specified scheme/Galois comparison

Source: main-20261015, graph-Frobenius-operator proof, Step 2, restriction calculation;
absolute-Frobenius trivialization pullback naturality, Stacks Tag 0F6W.
(blueprint: lem-trf-scheme-galois-pullback-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- The pullback-square comparison with horizontal tensor pullbacks and vertical intrinsic
pullbacks. The coordinate changes are the specified unit-preserving comparisons.
Source: main-20261015, graph-Frobenius-operator proof, Step 2;
(blueprint: lem-trf-scheme-galois-pullback-naturality). -/
def constantIntrinsicSquarePullback (A : Type u) [CommRing A] [Finite A]
    {U' U Y' Y : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ Y')
    (j : U ⟶ Y) (g : Y' ⟶ Y) (w : gU ≫ j = j' ≫ g) :
    sfIntrinsicDerivedPullback A j ⋙ proEtaleConstantRingDerivedPullback A gU ≅
      proEtaleConstantRingDerivedPullback A g ⋙ sfIntrinsicDerivedPullback A j' :=
  Functor.isoWhiskerLeft (sfIntrinsicDerivedPullback A j)
      (openSquareDerivedPullbackModel A gU) ≪≫
    sfIntrinsicDerivedSquarePullback A gU j' j g w ≪≫
    Functor.isoWhiskerRight (openSquareDerivedPullbackModel A g).symm
      (sfIntrinsicDerivedPullback A j')

end AlgebraicGeometry.Scheme

namespace WeilConjectures.FiniteFieldDatum

private theorem relativeFrobeniusIso_ext
    {X : Scheme.{u}} (f : X ⟶ X)
    (r s : 𝟭 X.ProEt ≅ proEtaleBaseChange f)
    (h : ∀ V : X.ProEt,
      (r.hom.app V).left ≫ pullback.fst V.hom f =
        (s.hom.app V).left ≫ pullback.fst V.hom f) : r = s := by
  apply Iso.ext
  apply NatTrans.ext
  funext V
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · exact h V
  · exact (r.hom.app V).w.trans (s.hom.app V).w.symm

private theorem normalizedFrobeniusIso_ext
    (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ X)
    (r : 𝟭 X.ProEt ≅ proEtaleBaseChange f)
    (s t : proEtaleConstantRingPullback A f ≅ 𝟭 _)
    (hs : ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A))
      (V : X.ProEt) (m : M.val.obj (Opposite.op V)),
      ((proEtaleConstantRingAdjunction A f).unit.app M ≫
        (proEtaleConstantRingPushforward A f).map (s.hom.app M)).val.app
          (Opposite.op V) m = M.val.map (r.inv.app V).op m)
    (ht : ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A))
      (V : X.ProEt) (m : M.val.obj (Opposite.op V)),
      ((proEtaleConstantRingAdjunction A f).unit.app M ≫
        (proEtaleConstantRingPushforward A f).map (t.hom.app M)).val.app
          (Opposite.op V) m = M.val.map (r.inv.app V).op m) : s = t := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((proEtaleConstantRingAdjunction A f).homEquiv M M).injective
  simp only [Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext m
  exact (hs M V.unop m).trans (ht M V.unop m).symm

set_option maxHeartbeats 800000 in
-- The selected comparison carries nested normalization witnesses and coefficient transports.
private theorem canonicalComparison_normalization
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Z₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, IsUnit (n : D.k) ∧ ∀ a : A, n • a = 0)
    (m : ℕ) (hm : 1 ≤ m) :
    let X := (D.geometricFiber Z₀).left
    let hX : X.IsCharacteristic D.p :=
      ⟨D.prime, natCast_eq_zero_of_natCast_top_eq_zero
        (D.model_characteristic (pullback.fst Z₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ Z₀.hom))⟩
    let H := X.iterateFrobenius D.prime (hX.2 ⊤) (D.a * m)
    let G := HPow.hPow (α := End X) (D.geometricGaloisFrobenius Z₀) m
    let datum := absoluteFrobenius_proEtale_trivialization_pullback D.p D.prime A
    let τ := datum.choose_spec.2.choose_spec.2.choose X hX (D.a * m)
    ∃ w : D.schemeFrobeniusIterate Z₀ m = H ≫ G,
      (D.canonicalSchemeGaloisComparison Z₀ A hA m hm).hom =
        eqToHom (congrArg (proEtaleConstantRingDerivedPullback A) w) ≫
          (proEtaleConstantRingPullbackComposition H G A).inv ≫
          Functor.whiskerLeft (proEtaleConstantRingDerivedPullback A G)
            (proEtaleFrobeniusDerivedIso A τ).hom ≫ (Functor.rightUnitor _).hom := by
  dsimp only [id]
  let datum := absoluteFrobenius_proEtale_trivialization_pullback D.p D.prime A
  let X := (D.geometricFiber Z₀).left
  let hX : X.IsCharacteristic D.p :=
    ⟨D.prime, natCast_eq_zero_of_natCast_top_eq_zero
      (D.model_characteristic (pullback.fst Z₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ Z₀.hom))⟩
  have h := (D.schemeGaloisComparison Z₀ A hA).choose_spec.choose_spec.2.2.2.2.2 m hm
  obtain ⟨r, hr⟩ := h
  obtain ⟨τ, hr, hτ, w, hw⟩ := hr
  have hr' : r = datum.choose X hX (D.a * m) := by
    apply relativeFrobeniusIso_ext
    intro V
    obtain ⟨hV, hVeq⟩ := hr V
    obtain ⟨hV', hVeq'⟩ := datum.choose_spec.1 X hX (D.a * m) V
    exact hVeq.trans hVeq'.symm
  have hτ' : τ = datum.choose_spec.2.choose_spec.2.choose X hX (D.a * m) := by
    apply normalizedFrobeniusIso_ext A _ r τ _ hτ
    intro M V a
    rw [hr']
    exact datum.choose_spec.2.choose_spec.2.choose_spec.1 X hX (D.a * m) M V a
  refine ⟨w, ?_⟩
  change _ = _ at hw
  rw [hτ'] at hw
  exact hw

/-- The canonical comparison commutes with pullback along a morphism of models. No
Cartesian or open condition is required: the two equalities of scheme maps suffice.

Source: main-20261015, def-pur-scheme-geometric-frobenius, final displayed
pullback-naturality equation, applied to positive iterates; graph-Frobenius-operator
proof, Step 2; `lem-pur-frobenius-trivialization-pullback`, Stacks Tag 0F6W.
(blueprint: lem-trf-scheme-galois-pullback-naturality).

Proof: express each kappa as the canonical composition for Phi = H followed by g,
then the normalized absolute-Frobenius trivialization at g-pullback. Relative Frobenius
on each weakly etale object is fixed by its two projections. Thus the site maps and
unit-normalized trivializations in the selected comparisons agree with those in
absoluteFrobenius_proEtale_trivialization_pullback. Its pullback-naturality equation
moves the H-trivialization through the pullback of the model map. Reassociate the
three pullbacks using their canonical composition maps: on ordinary tensor sections
both routes send ((v tensor a) tensor b) tensor c to
v tensor c_h(c_k(a))c_h(b)c. The coefficient maps preserve constants. The same maps
on fibre products have the same projections, so the reassociations agree. The
unit-preserving coordinate maps to intrinsic pullback carry this equation to the
mixed square displayed here. Apply the equations degreewise and descend through
localization; flat K-flat resolutions identify these exact descents with the
specified canonical derived composition. Naturality of the H-trivialization then
identifies the two displayed composites. This argument permits empty schemes,
identity maps, arbitrary model morphisms, and every positive m. -/
theorem canonicalSchemeGaloisComparison_pullback
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (j₀ : X₀ ⟶ Y₀) (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, IsUnit (n : D.k) ∧ ∀ a : A, n • a = 0)
    (m : ℕ) (hm : 1 ≤ m)
    (wP : D.schemeFrobeniusIterate X₀ m ≫
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left ≫
        D.schemeFrobeniusIterate Y₀ m)
    (wG : (HPow.hPow (α := End (D.geometricFiber X₀).left)
        (D.geometricGaloisFrobenius X₀) m) ≫
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left ≫
        (HPow.hPow (α := End (D.geometricFiber Y₀).left)
          (D.geometricGaloisFrobenius Y₀) m)) :
    (constantIntrinsicSquarePullback A (D.schemeFrobeniusIterate X₀ m) _ _
        (D.schemeFrobeniusIterate Y₀ m) wP).hom ≫
      Functor.whiskerRight (D.canonicalSchemeGaloisComparison Y₀ A hA m hm).hom
        (sfIntrinsicDerivedPullback A
          (((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap D.k₀ D.k)))).map j₀).left)) =
    Functor.whiskerLeft
        (sfIntrinsicDerivedPullback A
          (((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap D.k₀ D.k)))).map j₀).left))
        (D.canonicalSchemeGaloisComparison X₀ A hA m hm).hom ≫
      (constantIntrinsicSquarePullback A
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) m) _ _
        (HPow.hPow (α := End (D.geometricFiber Y₀).left)
          (D.geometricGaloisFrobenius Y₀) m) wG).hom := by
  sorry

end WeilConjectures.FiniteFieldDatum
