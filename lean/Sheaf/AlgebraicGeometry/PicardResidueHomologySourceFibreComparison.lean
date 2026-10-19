module

public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullbackFunctorial
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import Sheaf.AlgebraicGeometry.Picard.FlatInvertibleCanonicalDerivedBaseChange
import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Derived fibre of a line-bundle direct image

Source: Stacks Project, Tags 0A1D, 0B91, 0BF2 and 01XK.
(blueprint: new-picard-residue-homology-comparison-source-fibre)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem derivedFiberDirectImageCohomology
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {Y W : Scheme.{v}} (q : Y ⟶ W) [Flat q] [QuasiCompact q] [IsSeparated q]
    (M : Y.Modules) [M.IsInvertible] (w : W) (n : ℕ) :
    Nonempty (derivedFiberCohomology W
      ((schemeDerivedDirectImage q).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) 0).obj M)) n w ≃+
      ((Modules.pullback (pullback.fst q (W.fromSpecResidueField w))).obj M).H n) := by
  let g := W.fromSpecResidueField w
  let a := pullback.fst q g
  let p := pullback.snd q g
  let N := (Modules.pullback a).obj M
  have : EnoughInjectives (pullback q g).Modules := Modules.enoughInjectives (X := _)
  have : SheafOfModules.IsInvertible.{v, v, v} M :=
    Modules.IsInvertible.sheafOfModules_isInvertible M
  have : IsIso (schemeDerivedBaseChangeMap q p g a (pullback.condition ..)
      ((DerivedCategory.singleFunctor _ 0).obj M)) :=
    Modules.isIso_derivedBaseChange_of_flat_invertible q g a p
      (IsPullback.of_hasPullback q g) M
  have : IsIso (Modules.canonicalSinglePullbackMap a M) :=
    Modules.isIso_canonicalSinglePullbackMap a M
  let e := asIso (schemeDerivedBaseChangeMap q p g a (pullback.condition ..)
      ((DerivedCategory.singleFunctor _ 0).obj M)) ≪≫
    (schemeDerivedDirectImage p).mapIso (asIso (Modules.canonicalSinglePullbackMap a M))
  let h := (DerivedCategory.homologyFunctor
    (SheafOfModules.{v} (moduleRings (Spec (W.residueField w)).toRingedSpace)) n).mapIso e
  let h' := h ≪≫ Functor.homologyRightDerivedFunctorObjSingleFunctorIso
    (RingedSpace.moduleDirectImage p.toLRSHom.toShHom) N n
  let z := (SheafOfModules.evaluation
    (moduleRings (Spec (W.residueField w)).toRingedSpace) (.op ⊤)).mapIso h'
  obtain ⟨c⟩ := Modules.nonempty_sections_higherDirectImage_iso_H p N n
  exact ⟨z.toLinearEquiv.toAddEquiv.trans c⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An immersion does not change the residue fibre, and the supplied trivialization
of a coefficient on the original fibre trivializes its iterated pullback.
Source: Mathlib residue-point naturality, pullback pasting and the module pullback API.

Proof: The stalk maps of the immersion k are surjective. The induced map on residue
fields at w is surjective and injective, hence an isomorphism. Compose with the
residue-field congruence for hw to obtain Spec kappa(w) ≅ Spec kappa(s). Naturality
of the residue point identifies its composite with the residue point of s with
the composite of the residue point of w and k. The pullback pasting lemma identifies
the iterated fibre with the pullback along this composite; pulling back the spectrum
isomorphism gives the required projection-preserving scheme isomorphism e.
Uniqueness of left adjoints identifies tensor pullback with ordinary module pullback.
The pullback composition comparison and the projection equation identify the iterated
coefficient with e^* of the coefficient on X_s. Apply e^* to tau, then use the
structure-unit pullback isomorphism to obtain the displayed trivialization. This uses
neither properness nor flatness nor invertibility away from the original fibre.
For an empty fibre all the comparisons are still isomorphisms of zero modules;
nonclosed points and nonreduced schemes are covered by the same residue-field argument. -/
private theorem exists_immersion_residue_fibre_trivialization
    {X S : Scheme.{v}} (f : X ⟶ S) (L : X.Modules)
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf) :
    ∃ e : pullback (pullback.snd f k) (W.fromSpecResidueField w) ≅
        pullback f (S.fromSpecResidueField s),
      e.hom ≫ pullback.fst f (S.fromSpecResidueField s) =
        pullback.fst (pullback.snd f k) (W.fromSpecResidueField w) ≫ pullback.fst f k ∧
      Nonempty (((Modules.pullback
        (pullback.fst (pullback.snd f k) (W.fromSpecResidueField w))).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L)) ≅
        SheafOfModules.unit
          (pullback (pullback.snd f k) (W.fromSpecResidueField w)).ringCatSheaf) := by
  classical
  subst s
  have hr : Function.Surjective (k.residueFieldMap w) := by
    intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective (R := W.presheaf.stalk w) y
    obtain ⟨x, rfl⟩ := k.stalkMap_surjective w z
    exact ⟨IsLocalRing.residue _ x, rfl⟩
  have : IsIso (k.residueFieldMap w) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨(k.residueFieldMap w).hom.injective, hr⟩
  let g := W.fromSpecResidueField w
  let j := S.fromSpecResidueField (k w)
  let b := Spec.map (k.residueFieldMap w)
  have hb : g ≫ k = b ≫ j := (k.SpecMap_residueFieldMap_fromSpecResidueField w).symm
  let d := pullback.map f (g ≫ k) f j (𝟙 X) b (𝟙 S) (by simp) (by simpa using hb)
  have : IsIso d := by dsimp only [d]; infer_instance
  let e := pullbackLeftPullbackSndIso f k g ≪≫ asIso d
  have he : e.hom ≫ pullback.fst f j =
      pullback.fst (pullback.snd f k) g ≫ pullback.fst f k := by
    simp [e, d]
  refine ⟨e, he, ?_⟩
  let a := pullback.fst (pullback.snd f k) g
  let c := pullback.fst f k
  let cs := pullback.fst f j
  let t := (Classical.choose (Modules.exists_tensorPullbackAdjunction c)).leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction c)
  let ts := (Classical.choose (Modules.exists_tensorPullbackAdjunction cs)).leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction cs)
  exact ⟨(Modules.pullback a).mapIso (t.app L) ≪≫
    (Modules.pullbackComp a c).app L ≪≫
    (Modules.pullbackCongr he.symm).app L ≪≫
    (Modules.pullbackComp e.hom cs).symm.app L ≪≫
    (Modules.pullback e.hom).mapIso ((ts.app L).symm ≪≫ τ) ≪≫
    Modules.pullbackObjUnitIso e.hom⟩

attribute [local irreducible] structureSheafCohomologyPullback

private def addEquivOfInverse {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (g : B →+ A) (hl : g.comp f = AddMonoidHom.id A)
    (hr : f.comp g = AddMonoidHom.id B) : A ≃+ B where
  toFun := f
  invFun := g
  left_inv x := DFunLike.congr_fun hl x
  right_inv x := DFunLike.congr_fun hr x
  map_add' := f.map_add

private noncomputable def structureCohomologyIso {Y Z : Scheme.{v}} (e : Y ≅ Z)
    (n : ℕ) : Sheaf.H (structureSheafAb Y) n ≃+ Sheaf.H (structureSheafAb Z) n :=
  addEquivOfInverse (structureSheafCohomologyPullback e.inv n)
    (structureSheafCohomologyPullback e.hom n)
    ((structureSheafCohomologyPullback_functorial.2 e.hom e.inv n).symm.trans
      ((congrArg (fun f : Y ⟶ Y ↦ structureSheafCohomologyPullback f n)
        e.hom_inv_id).trans (structureSheafCohomologyPullback_functorial.1 Y n)))
    ((structureSheafCohomologyPullback_functorial.2 e.inv e.hom n).symm.trans
      ((congrArg (fun f : Z ⟶ Z ↦ structureSheafCohomologyPullback f n)
        e.inv_hom_id).trans (structureSheafCohomologyPullback_functorial.1 Z n)))


/-- The derived fibre of the pulled-back invertible coefficient computes
structure-sheaf cohomology using the supplied fibre trivialization.
Source: Stacks Project, Tags 0A1D, 0B91, 0BF2 and 01XK.
(blueprint: new-picard-residue-homology-comparison-source-fibre)

Proof: Put fW = pullback.snd f k and G = pullback.fst f k applied to L.
Tensor pullback agrees with ordinary module pullback by uniqueness of left
adjoints; hence G is invertible. The morphism fW is proper, flat and locally
of finite presentation, by stability under base change. In particular it
is quasi-compact and separated. Set g = W.fromSpecResidueField w and form
its cartesian square with fW, with projections a and q. Apply
Modules.isIso_derivedBaseChange_of_flat_invertible to this square and G.
Modules.isIso_canonicalSinglePullbackMap identifies derived pullback of
G[0] with ordinary pullback of G in degree zero, since G is invertible.
Thus Li_w^* RfW_*G is Rq_* of (a^*G)[0]. This is the arbitrary base-change
comparison of Tag 0A1D; Tag 0B91 also supplies it in the proper case.
The residue map of the immersion k is an isomorphism. Compose it with the
residue congruence from hw, obtaining a field isomorphism from kappa(s) to
kappa(w). Naturality of residue points identifies g followed by k with the
residue point of s preceded by the spectrum of this field isomorphism.
The unique projection-preserving pullback isomorphisms identify the fibre
of fW over w with X_s after that spectrum isomorphism. Pullback composition
therefore identifies a^*G with the pullback of L_s. Pull back the supplied
trivialization tau and use the structure-unit pullback isomorphism to
identify this coefficient with the structure sheaf of that fibre.
Apply degree-one homology and sections on Spec kappa(w). The unbounded
right-derived functor comparison on a single module identifies this
homology with R^1 q_*O. Scheme module sheaves have injective resolutions.
Apply Modules.exists_addEquiv_sections_higherDirectImage_H (Tag 01XK)
to q and its quasi-coherent structure module. This gives Sheaf.H of the
underlying additive structure sheaf, since Modules.H is defined using
that abelian sheaf cohomology. The unit module's underlying sheaf is
the structure sheaf with only its additive group structure retained.
Finally transport
along the fibre scheme isomorphism just constructed to X_s and forget
scalars. This yields precisely the displayed additive equivalence; no
choice of an affine representative K, or of frames of K, is involved.
For an empty fibre both cohomology groups are zero, and the comparison
also handles nonreduced bases and nonclosed points. -/
theorem picard_residue_homology_source_fibre_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    Nonempty (derivedFiberCohomology W E 1 w ≃+
      Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  dsimp only
  let M := (Modules.tensorPullback (pullback.fst f k)).obj L
  have : M.IsInvertible := by
    let t := (Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.fst f k))).leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction (pullback.fst f k))
    exact Modules.IsInvertible.of_iso (t.app L).symm
  obtain ⟨c⟩ := derivedFiberDirectImageCohomology (pullback.snd f k) M w 1
  obtain ⟨e, _, ⟨t⟩⟩ := exists_immersion_residue_fibre_trivialization f L W k w s hw τ
  let d := (Modules.H.mapLinearEquiv t 1).toAddEquiv
  exact ⟨c.trans (d.trans (structureCohomologyIso e 1))⟩

end AlgebraicGeometry.Scheme

