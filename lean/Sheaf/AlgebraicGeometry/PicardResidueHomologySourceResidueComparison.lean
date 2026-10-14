module

public import Sheaf.AlgebraicGeometry.AffineResidueCycleHomology
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel
import Sheaf.AlgebraicGeometry.PicardResidueSourceModelHomology
import Sheaf.AlgebraicGeometry.PicardResidueQuotientModelHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.AlgebraicGeometry.PicardResidueHomologySourceFibreComparison
import Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative
import Sheaf.AlgebraicGeometry.LocalizedStrictPerfectResidueHomology
import Sheaf.AlgebraicGeometry.RelativeMVMaps
import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-! # A strictly perfect affine model computes residue cycle homology

Source: Stacks Project, Tags 01IB, 064K, 06YJ and 010V.
(blueprint: new-picard-residue-homology-comparison-source-residue)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The explicit degree-one residue quotient computes the derived fibre of a
represented object, independently of any geometric direct-image presentation.
Source: Stacks Project, Tags 01IB, 064K, 06YJ and 010V.
(blueprint: new-picard-residue-homology-comparison-source-residue)

Proof: Set A = Gamma(W,U) and let P be terminal sections of K, with the
section differentials. The finite free retractions in hK remain retractions
under sections, so every P.X j is a finite projective A-module, hence flat.
The bounds in hK give bounds for P. Thus P is K-flat by Tag 064K.
Transport the affine associated-sheaf adjunction to the localized site. Its
counit reconstructs finite free sheaves from their sections. Naturality makes
this counit invertible also on their retracts: the inverse on a retract is
obtained by composing the inclusion, the free counit's inverse and the
projection. Hence its components on K are invertible, and counit naturality
makes them a complex isomorphism from sheafified P to K (Tag 01IB).
Compose its derived image with hE. Apply affine_kFlat_residuePullback_model
to P and this representative. The resulting model of the derived fibre is
the associated sheaf of P tensored with the residue field at the affine
chart point. Affinity identifies that point's prime with the kernel of
W.evaluation U w hwU, which is p by hp. The chart and open-immersion residue
isomorphisms identify its field with W.residueField w, compatibly with A's
action. Therefore the model's section complex, after forgetting scalars,
is canonically isomorphic to the complex with terms affineResidueTerm.
These term comparisons are natural in module maps, so identify its
differentials with affineResidueDifferential, including degrees 0,1,2.
Sections on the one-point residue spectrum are exact; taking degree-one
homology therefore computes derivedFiberCohomology W E 1 w. Finally d^2=0
puts incoming boundaries in outgoing cycles. Module homology is the quotient
of these cycles by these boundaries (Tag 010V); its canonical projection has
exactly the kernel described by affineResidueCycleClass_surjective_kernel.
The first isomorphism theorem gives the stated additive equivalence. The
argument does not assume that differentials vanish or that projective terms
are free; it includes the zero complex and rank-zero retracts. -/
theorem picard_residue_homology_source_residue_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    Nonempty (affineResidueCycleHomology W U p K ≃+
      derivedFiberCohomology W E 1 w) := by
  obtain ⟨eQ⟩ := picard_residue_quotient_model_homology W E w U hwU hU p hp K
  obtain ⟨eS⟩ := picard_residue_source_model_homology W E w U hwU hU K hK hE
  exact ⟨eQ.trans eS.symm.toAddEquiv⟩

set_option backward.isDefEq.respectTransparency false in
/-- The base-changed coefficient morphism lies over W.
Source: Stacks Project, Tag 01F7; the pullback functor's projection equation. -/
private theorem bypassPicardCoefficientBaseMap_snd
    {X X' S : Scheme.{v}} (f : X ⟶ S) (f' : X' ⟶ S)
    (u : X' ⟶ X) (hu : u ≫ f = f') (W : Scheme.{v}) (k : W ⟶ S) :
    (((Over.pullback k).map
      (Over.homMk (U := Over.mk f') (V := Over.mk f) u hu)).left) ≫
        pullback.snd f k = pullback.snd f' k := by simp

/-- The other projection identifies the two pulled-back coefficients.
Source: Stacks Project, Tag 01F7; the pullback functor's projection equation. -/
private theorem bypassPicardCoefficientBaseMap_fst
    {X X' S : Scheme.{v}} (f : X ⟶ S) (f' : X' ⟶ S)
    (u : X' ⟶ X) (hu : u ≫ f = f') (W : Scheme.{v}) (k : W ⟶ S) :
    (((Over.pullback k).map
      (Over.homMk (U := Over.mk f') (V := Over.mk f) u hu)).left) ≫
        pullback.fst f k = pullback.fst f' k ≫ u := by simp

set_option backward.isDefEq.respectTransparency false in
/-- Construct the coefficient-induced arrow between base-changed direct images.
Source: Stacks Project, Tags 01F7 and 08HY.
(blueprint: lem-sc-picard-residue-homology-chosen-geometric-maps)

Construction: Let j:X'_W -> X_W be the pullback of u. The two projection
identities identify j^*(L_W) with (u^*L)_W by ordinary pullback composition and
the canonical isomorphisms from tensor pullback to ordinary pullback. Compose
the canonical derived-single pullback map with that coefficient isomorphism.
Apply the derived adjunction unit along j and direct-image composition, then
transport j followed by f_W to f'_W using its projection equation. This gives
the displayed arrow without any cohomology or affine-model comparison. There
is no properness, flatness or invertibility hypothesis on this construction. -/
private noncomputable def bypassPicardDerivedCoefficientMap
    [∀ Y : Scheme.{v}, HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X X' S : Scheme.{v}} (f : X ⟶ S) (f' : X' ⟶ S)
    (u : X' ⟶ X) (hu : u ≫ f = f') (L : X.Modules)
    (W : Scheme.{v}) (k : W ⟶ S) :
    (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L)) ⟶
    (schemeDerivedDirectImage (pullback.snd f' k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f' k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f' k)).obj
            ((Modules.tensorPullback u).obj L))) := by
  classical
  let j := ((Over.pullback k).map
    (Over.homMk (U := Over.mk f') (V := Over.mk f) u hu)).left
  have hj : j ≫ pullback.snd f k = pullback.snd f' k :=
    bypassPicardCoefficientBaseMap_snd f f' u hu W k
  have hc : j ≫ pullback.fst f k = pullback.fst f' k ≫ u :=
    bypassPicardCoefficientBaseMap_fst f f' u hu W k
  let M := (Modules.tensorPullback (pullback.fst f k)).obj L
  let Li := (Modules.tensorPullback u).obj L
  let Mi := (Modules.tensorPullback (pullback.fst f' k)).obj Li
  let t (Y Z : Scheme.{v}) (g : Y ⟶ Z) :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction g)).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction g)
  let α : (Modules.pullback j).obj M ≅ Mi :=
    (Modules.pullback j).mapIso ((t _ _ (pullback.fst f k)).app L) ≪≫
      (Modules.pullbackComp j (pullback.fst f k)).app L ≪≫
      (Modules.pullbackCongr hc).app L ≪≫
      ((Modules.pullbackComp (pullback.fst f' k) u).app L).symm ≪≫
      (Modules.pullback (pullback.fst f' k)).mapIso ((t _ _ u).app L).symm ≪≫
      ((t _ _ (pullback.fst f' k)).app Li).symm
  let A := (DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj M
  let Ai := (DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings (pullback f' k).toRingedSpace)) 0).obj Mi
  let a : (derivedPullback j).obj A ⟶ Ai :=
    Modules.canonicalSinglePullbackMap j M ≫
      (DerivedCategory.singleFunctor _ 0).map α.hom
  exact relativeMVUnit j (pullback.snd f k) A ≫
    (schemeDerivedDirectImage (j ≫ pullback.snd f k)).map a ≫
      eqToHom (congrArg (fun g ↦ (schemeDerivedDirectImage g).obj Ai) hj)


set_option maxHeartbeats 800000 in
-- The chosen geometric square compares derived pullback and explicit tensor quotients.
/-- Choose only the chain maps and compatible fibre comparisons used by the Picard
finite-free calculation. The source comparison is common to the entire family.
Source: Stacks Project, Tags 0BF2, 0B91, 01XK, 06YJ and 010V.
(blueprint: lem-sc-picard-residue-homology-chosen-geometric-maps)

Proof: For each base-changed ui, transpose the coefficient pullback identity under
pullback/direct-image adjunction. Compose derived direct images to obtain E → Ei.
Restrict to U and conjugate by the supplied model isomorphisms. The affine perfect
representative theorem gives the chosen chain maps φi. Use one source trivialization
τ and its pullbacks to every target. The K-flat residue comparison is natural on
strictly perfect complexes, and the quotient comparison is chosen simultaneously
by picard_residue_quotient_model_homology_naturality. Compose it with derived base
change and the affine higher-direct-image comparison to obtain eK and eCi. Naturality
identifies the chosen maps with structure-sheaf pullback. The immersion and affine
evaluation identify the residue fields. The empty family still has the source
comparison. No compatibility with every representative or with arbitrary additive
equivalences is asserted. This is the single remaining geometric compatibility
obligation of the direct fixed-model route; the quotient naturality is proved. -/
theorem picard_residue_homology_chosen_geometric_maps
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i)))
 :
    ∃ (eK : affineResidueCycleHomology W U p K ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (eC : ∀ i, affineResidueCycleHomology W U p (C i) ≃+
        Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)
      (φ : ∀ i, K ⟶ C i),
      ∀ i z, eC i (affineResidueCycleHomologyMap (φ i) z) =
        structureSheafCohomologyPullback
          (((Over.pullback (S.fromSpecResidueField s)).map
            (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
              (ui i) (hui i))).left) 1 (eK z) := by
  classical
  obtain ⟨m⟩ := hE
  let mi := fun i ↦ Classical.choice (hCi i)
  let R := (SheafOfModules.overFunctor.{v}
    (moduleRings W.toRingedSpace) U).mapDerivedCategory
  let a := fun i ↦ m.inv ≫ R.map
    (bypassPicardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) ≫ (mi i).hom
  choose φ hφ using fun i ↦
    perfect_affine_map_representative W U hU K (C i) hK (hC i) (a i)
  suffices h : ∃ (eK : affineResidueCycleHomology W U p K ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (eC : ∀ i, affineResidueCycleHomology W U p (C i) ≃+
        Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1),
      ∀ i z, eC i (affineResidueCycleHomologyMap (φ i) z) =
        structureSheafCohomologyPullback
          (((Over.pullback (S.fromSpecResidueField s)).map
            (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
              (ui i) (hui i))).left) 1 (eK z) by
    obtain ⟨eK, eC, h⟩ := h
    exact ⟨eK, eC, φ, h⟩
  -- The arrows and their representatives are constructed above. What remains is
  -- compatibility of the coherent residue and geometric cohomology comparisons.
  sorry

end AlgebraicGeometry.Scheme
