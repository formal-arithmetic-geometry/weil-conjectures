module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.NoetherianPerfectDirectImage

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso
import Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel
import Sheaf.AlgebraicGeometry.PerfectOfOpenPullbacks
import Sheaf.AlgebraicGeometry.PerfectImpliesQCoh
import Sheaf.AlgebraicGeometry.DerivedPullbackPerfect

/-! # Perfect direct image with proper support

Source: literature/stacks-project/perfect.tex, Lemma 36.30.1, Tag 0A1H
(blueprint: lem-pc-proper-support-perfect-direct-image).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- The direct image of a perfect complex tensored with a bounded, finitely presented,
base-flat complex with proper support is perfect and satisfies arbitrary base change.
Source: Stacks Project, Lemma 36.30.1, Tag 0A1H.
The new complex is ordinary termwise pullback of G, as in Tag 0A1D.

Proof: arbitrary base change is Tag 0A1D (lem-pc-rf-base-change-complex). Spread the
finite-presentation, flatness, support and perfectness data by Noetherian approximation
(thm-pd-spreading-out and lem-pc-noetherian-approximation-data). Apply the Noetherian
perfect-direct-image theorem (Tag 0DJQ), then descend perfectness and glue it Zariski-locally.
(blueprint: lem-pc-proper-support-perfect-direct-image). -/
theorem properSupport_perfect_directImage
    {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : Scheme.IsPerfect X E)
    (G : CochainComplex X.Modules ℤ)
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    (hGflat : ∀ n : ℤ, (G.X n).IsFlatOver f)
    (hGproper : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver f (G.X n)) :
    Scheme.IsPerfect S ((schemeDerivedDirectImage f).obj
      (E ⊗ (DerivedCategory.Q.obj G))) ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        Nonempty ((derivedPullback g).obj
            ((schemeDerivedDirectImage f).obj (E ⊗ (DerivedCategory.Q.obj G))) ≅
          (schemeDerivedDirectImage (pullback.snd f g)).obj
            ((derivedPullback (pullback.fst f g)).obj E ⊗
              DerivedCategory.Q.obj
                (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomologicalComplex
                  (.up ℤ)).obj G))) := by
  constructor
  · apply perfect_of_open_pullbacks
    intro x
    obtain ⟨U, hx, Xi, Si, fi, hSi, hfp, hqc, hqs, hft, Ei, hEi,
      Gi, hGib, hGifp, hGiflat, hGiproper, g, ⟨e⟩⟩ :=
      properSupport_local_noetherian_model f E hE G hGb hGflat hGproper x
    let : IsNoetherian Si := hSi
    let : LocallyOfFinitePresentation fi := hfp
    let : QuasiCompact fi := hqc
    let : QuasiSeparated fi := hqs
    let : LocallyOfFiniteType fi := hft
    let : ∀ n : ℤ, (Gi.X n).IsFinitePresentation := hGifp
    have hi := noetherian_perfect_directImage fi Ei hEi Gi hGib hGiflat hGiproper
    have hg := derivedPullback_preserve_perfect g _ hi
    refine ⟨U, hx, ?_⟩
    intro y
    obtain ⟨V, hy, P, hP, ⟨c⟩⟩ := hg y
    exact ⟨V, hy, P, hP, ⟨(SheafOfModules.overFunctor
      (moduleRings U.toScheme.toRingedSpace) V).mapDerivedCategory.mapIso e ≪≫ c⟩⟩
  · intro T g
    obtain ⟨a, b, hb⟩ := hGb
    apply relativelyFlat_tensor_baseChange_iso f g E
      (schemeDerivedQCohProperty_of_isPerfect X E hE) G
      ⟨b, fun n hn ↦ hb n (Or.inr hn)⟩
      (fun n ↦ inferInstance) hGflat

end AlgebraicGeometry
