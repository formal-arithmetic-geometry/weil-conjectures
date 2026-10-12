/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility

/-! # The degree-zero exchange factorization through strict-local sections

Source: Stacks Project, Tags 03Q9, 03Q1 and 0A3U.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Global sections to the identity geometric stalk on the spectrum of a closed field.
This is the global-section identification followed by the identity-neighbourhood germ.
Source: Stacks Project, Tag 03QO.
(blueprint: lem-weil-pbc-qcqs-geometric-exchange-factorization). -/
noncomputable def geometricPointGlobalGerm
    (Λ : Type (u + 1)) [CommRing Λ] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (G : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj G ⟶
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.obj G :=
  (Sheaf.ΓNatIsoSheafSections _ _
    (IsTerminal.isTerminalOfObj
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
      (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) Over.mkIdTerminal)).hom.app G ≫
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
      (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
      (Over.homMk (𝟙 _) (Category.comp_id _)) G.obj

/-- For a qcqs morphism, exchange on the identity geometric stalk factors through
sections over the strict henselization and restriction to the given geometric fibre.
There is no properness hypothesis and no invertibility claim for the fibre restriction.
Source: Stacks Project, Tags 03Q9, 03Q1 and 0A3U
(blueprint: lem-weil-pbc-qcqs-geometric-exchange-factorization).

Proof: the pointed affine-neighbourhood colimit constructs the strict-local ring and
its distinguished map from Spec Ω. Its maximal ideal is the kernel of the residue map,
so this is its geometric closed point. The neighbourhood maps show that its composite
with the structural morphism is s. Form the pullback with X; the universal property
provides q and its cartesian square. The qcqs section-continuity comparison (03Q9)
identifies the direct-image stalk with global sections on this pullback. Forgetting
modules commutes with the filtered colimit and the inverse-image constructions, so
this bijective comparison is a module isomorphism. On an affine representative it is
adjunction unit followed by restriction along the corresponding limit leg.
The inverse-image stalk formula (03Q1) identifies the source stalk of exchange with
this direct-image stalk. Expand exchange as unit, square comparison and counit.
On every representative the result restricts its section to the same pointed fibre.
The upperStarComp inverse identifies the iterated inverse image with g' inverse image;
the lowerStar global-section comparison and the terminal germ give the target stalk.
The colimit's jointly epimorphic germs give the displayed equality. This proves only
the factorization: the restriction to the geometric closed fibre need not be invertible
without properness, and is handled separately. -/
theorem qcqs_geometricExchange_factorization
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let R := Scheme.strictHenselizationRing s
    let ρ := Scheme.strictHenselizationStructuralMap s
    let Z := pullback f ρ
    let p := pullback.fst f ρ
    let H := (upperStar (ModuleCat.{u + 1} Λ) p).obj F
    ∃ (_ : IsLocalRing R), IsStrictlyHenselianLocalRing R ∧
      ∃ (t : Spec (.of Ω) ⟶ Spec R) (q : X' ⟶ Z),
        t default = IsLocalRing.closedPoint R ∧
        IsPullback q f' (pullback.snd f ρ) t ∧
        ∃ (hq : q ≫ p = g')
          (e : (Scheme.pointSmallEtale ((𝟙 (Spec (.of Ω))) ≫ s)).sheafFiber.obj
              ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≅
            (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj H),
          (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
              ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) =
            (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) s
              (𝟙 (Spec (.of Ω)))).hom.app ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
            e.hom ≫ globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q H ≫
            (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
              ((upperStarComp (ModuleCat.{u + 1} Λ) q p g' hq.symm).inv.app F) ≫
            (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f').inv.app
              ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) ≫
            geometricPointGlobalGerm Λ Ω
              ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
                ((upperStar (ModuleCat.{u + 1} Λ) g').obj F))  := by
  classical
  dsimp only
  let : Algebra (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
  obtain ⟨hlocal, hstrict, _, _, σ, ⟨hpoint, hbase⟩, _⟩ :=
    strictHenselizationResidue s rfl
  let := hlocal
  let t := Spec.map (CommRingCat.ofHom
    (((IntermediateField.val
      (separableClosure (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
        σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing s))))
  have ht : t default = IsLocalRing.closedPoint (Scheme.strictHenselizationRing s) := by
    rw [Subsingleton.elim (default : Spec (.of Ω)) (IsLocalRing.closedPoint Ω)]
    change PrimeSpectrum.comap
      ((((IntermediateField.val
        (separableClosure (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom).comp
          σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing s)))
      (IsLocalRing.closedPoint Ω) = _
    rw [PrimeSpectrum.comap_comp]
    exact IsLocalRing.PrimeSpectrum.comap_residue _ _
  have htbase : t ≫ Scheme.strictHenselizationStructuralMap s = s := hbase
  let q := pullback.lift g' (f' ≫ t)
    (sq.w.trans (by rw [Category.assoc, htbase]))
  have hq : q ≫ pullback.fst f (Scheme.strictHenselizationStructuralMap s) = g' :=
    pullback.lift_fst _ _ _
  have hqt : q ≫ pullback.snd f (Scheme.strictHenselizationStructuralMap s) = f' ≫ t :=
    pullback.lift_snd _ _ _
  have hcart : IsPullback q f'
      (pullback.snd f (Scheme.strictHenselizationStructuralMap s)) t := by
    apply IsPullback.of_right (s := ?_) hqt (IsPullback.of_hasPullback _ _)
    simpa only [hq, htbase] using sq
  refine ⟨hlocal, hstrict, t, q, ht, hcart, hq, ?_⟩
  obtain ⟨e₀, he₀⟩ := exists_qcqsStrictLocalModuleComparison Λ f s F
  let e : (Scheme.pointSmallEtale ((𝟙 (Spec (.of Ω))) ≫ s)).sheafFiber.obj
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≅
      (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F) :=
    (eqToIso (by rw [Category.id_comp])) ≪≫ e₀
  refine ⟨e, ?_⟩
  simpa only [e, Iso.trans_hom, eqToIso.hom, geometricPointGlobalGerm,
    Category.assoc] using
    strictLocal_exchange_compatibility Λ sq F t hpoint q hqt hq e₀.hom he₀

end AlgebraicGeometry.Etale
