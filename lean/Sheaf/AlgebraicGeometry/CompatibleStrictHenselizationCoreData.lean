module
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationCoreExistence
import WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationCoreCompletion
/-!
# Compatible strict henselization data

Use the upstream existence and functoriality theorems, transporting their affine colimit
presentations to the small coordinate-ring colimits without changing the public statement.

Source: Stacks Project, Tags 04HX, 03PS, 04GU and 04DY.
(blueprint: compatible-strict-henselization-core-data).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale
/-- The spectrum of the canonical comparison between the two affine colimits. -/
private noncomputable def localizationComparison
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : strictLocalization s ≅ strictHenselizationScheme s :=
  asIso (Spec.map (smallStrictHenselizationColimitIso s).hom)

/-- The comparison identifies the two structure morphisms, as checked on a limit leg. -/
@[reassoc] private theorem localizationComparison_base
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    (localizationComparison s).hom ≫ strictHenselizationStructuralMap s =
      strictLocalizationToBase s := by
  classical
  let : HasColimit (strictHenselizationDiagram s) := inferInstance
  let := (strictHenselization_properties s).2.1
  let j := Classical.choice (IsCofiltered.nonempty (C :=
    SmallModel.{u} (strictHenselizationNeighbourhoods s)))
  have hs : (strictHenselizationCone s).π.app (Opposite.op (Opposite.op j)) ≫
      Spec.map (ΓSpecIso
        (((equivSmallModel.{u}
          (strictHenselizationNeighbourhoods s)).inverse.obj j).1.left.unop)).inv ≫
      ((AffineEtale.Spec S).obj
        (((equivSmallModel.{u}
          (strictHenselizationNeighbourhoods s)).inverse.obj j).1)).hom =
      strictHenselizationStructuralMap s :=
    (exists_strictHenselizationStructuralMap s).choose_spec j
  rw [← hs]
  have hι : colimit.ι (strictHenselizationAffineDiagram s) (Opposite.op j) ≫
      (smallStrictHenselizationColimitIso s).hom =
      (smallStrictHenselizationCocone s).ι.app (Opposite.op j) := by
    let := strictHenselizationAffineInclusion_isEquivalence s
    exact Functor.Final.ι_colimitIso_hom
      ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
        strictHenselizationAffineInclusion s).op (strictHenselizationDiagram s) (Opposite.op j)
  have hleg : (localizationComparison s).hom ≫
      (strictHenselizationCone s).π.app (Opposite.op (Opposite.op j)) =
      (strictHenselizationAffineCone s).π.app (Opposite.op (Opposite.op j)) := by
    change Spec.map (smallStrictHenselizationColimitIso s).hom ≫
      Spec.map (colimit.ι (strictHenselizationAffineDiagram s) (Opposite.op j)) = _
    rw [← Spec.map_comp, hι]
    rfl
  rw [← Category.assoc, hleg]
  exact strictHenselizationStructuralMap_eq s j

/-- Construction of compatible strict henselization data from pointed affine etale neighbourhoods.
Source: Stacks Tags 04HX, 03PS, 04GU, 04DY. (blueprint: compatible-strict-henselization-core-data)

Proof: upstream core existence supplies henselian local rings, separably closed residue
fields, universal homeomorphisms, and presentations of the large affine colimits.
Upstream core completion supplies the local ring map over g. Compose the spectrum
presentations with Spec of smallStrictHenselizationColimitIso to obtain presentations
of the small coordinate-ring colimits. The colimit injection formula identifies the
corresponding cone legs. Composing a leg with its neighbourhood structure map identifies
the two structural maps, so all three equalities transport by associativity. The rings,
local map, residue maps and universal-homeomorphism proofs are retained unchanged.
-/
theorem Etale.exists_compatibleStrictHenselizationCoreData
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (hσ : ∃ (s : S) (ψ : S.residueField s ⟶ .of k),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ S.fromSpecResidueField s = σ)
    (hτ : ∃ (t : T) (ψ : T.residueField t ⟶ .of k'),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ T.fromSpecResidueField t = τ)
    (ν : Spec (.of Ω) ⟶ Spec (.of k')) :
    let s := ν ≫ ι ≫ σ
    let t := ν ≫ τ
    ∃ (A B : Type u) (cA : CommRing A) (cB : CommRing B),
      letI := cA
      letI := cB
      ∃ (hA : HenselianLocalRing A) (hB : HenselianLocalRing B),
        letI := hA
        letI := hB
        ∃ (sA : IsSepClosed (IsLocalRing.ResidueField A))
          (sB : IsSepClosed (IsLocalRing.ResidueField B)),
          letI := sA
          letI := sB
          ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
            letI := hφ
            ∃ (eA : Spec (.of A) ≅ strictHenselizationScheme s)
              (eB : Spec (.of B) ≅ strictHenselizationScheme t)
              (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
              (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))),
              IsUniversalHomeomorphism ρA ∧ IsUniversalHomeomorphism ρB ∧
              Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
                strictHenselizationStructuralMap s =
                eB.hom ≫ strictHenselizationStructuralMap t ≫ g ∧
              ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
                eA.hom ≫ strictHenselizationStructuralMap s = σ ∧
              ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
                eB.hom ≫ strictHenselizationStructuralMap t = τ := by
  dsimp
  obtain ⟨A, B, cA, cB, hA, hB, sA, sB, eA, eB, ρA, ρB, hUA, hUB, ha0, hb0⟩ :=
    Etale.exists_compatibleStrictHenselizationCoreExistence σ τ ι hι hσ hτ ν
  let := cA
  let := cB
  let := hA
  let := hB
  let := sA
  let := sB
  obtain ⟨φ, hφ, hbase⟩ :=
    Etale.exists_compatibleStrictHenselizationCoreCompletion
      (by simpa only [Category.assoc] using congrArg (ν ≫ ·) hι) eA eB
  refine ⟨A, B, cA, cB, hA, hB, sA, sB, φ, hφ,
    eA ≪≫ localizationComparison _, eB ≪≫ localizationComparison _, ρA, ρB,
    hUA, hUB, ?_, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Category.assoc, localizationComparison_base,
      localizationComparison_base_assoc] using hbase
  · simpa only [Iso.trans_hom, Category.assoc, localizationComparison_base] using ha0
  · simpa only [Iso.trans_hom, Category.assoc, localizationComparison_base] using hb0
end AlgebraicGeometry
