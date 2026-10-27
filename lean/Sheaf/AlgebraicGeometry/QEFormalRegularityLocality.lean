/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import Sheaf.AlgebraicGeometry.RigRegularFormalGeometry
public import Sheaf.AlgebraicGeometry.AdicFormalGeometry
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.RingTheory.GRing
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.RingTheory.RegularMapReducedTarget
import Sheaf.AlgebraicGeometry.FormalAffinePrincipalRefinement
import Sheaf.AlgebraicGeometry.QuasiExcellentFormalAffines
import Sheaf.AlgebraicGeometry.RegularMorphismFormalCompletion
import Sheaf.AlgebraicGeometry.GRingAffineCover
import Sheaf.AlgebraicGeometry.JTwoAffineCover
import WeilConjectures.RingTheory.FiniteTypeGRing
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber
import WeilConjectures.RingTheory.FlatUnderRegular
import WeilConjectures.RingTheory.GeometricallyRegularFieldExtension
import WeilConjectures.RingTheory.RegularBaseChange
import WeilConjectures.RingTheory.RegularComposition
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularLocalMaximal
import WeilConjectures.RingTheory.RegularMapAscent
import WeilConjectures.RingTheory.RegularPermanence
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Locality of quasi-excellent formal geometry

Source: Temkin, Non-embedded Desingularization, §§2.4.3, 2.4.9, 2.4.12,
Lemma 2.4.6, and §§3.1.1, 3.1.4
(blueprint: lem-per-qe-formal-regularity-locality).

The definitions of formal spectra, finite Noetherian atlases, complete chart rings,
regular ring maps, formal ideals and formal pairs are imported. Regularity is expressed
on every formal affine open, and its equivalent covering criterion is stated explicitly.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Quasi-excellence can be checked on any formal open cover, and on the chart rings of
any cover by formal affine opens.
Source: Temkin §2.4.3 (blueprint: lem-per-qe-formal-regularity-locality).

Proof: Refine an arbitrary chart and the given charts by common principal formal opens.
Their complete rings are quasi-excellent by quasiExcellent_formalCompletion. Modulo an
ideal of definition these are principal localizations of the original quotient ring.
The G-ring and J-2 affine-cover criteria imply quasi-excellence of that quotient. Gabber's
adic quasi-excellence theorem lifts it to the complete chart ring. For a cover by formal
affines this uses only the quasi-excellence of the covering chart rings. The reverse
implication follows by applying the same refinement argument to a restriction.
Empty covers are allowed. -/
theorem quasiExcellentAdicFormal_cover_iff (X : RingedSpace.{u})
    (_hX : IsNoetherianAdicFormalScheme X)
    (_qX : X ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace)
    (ι : Type v) (U : ι → Opens X) (_hU : (⨆ i, U i) = ⊤) :
    (IsQuasiExcellentAdicFormalScheme X ↔
      ∀ i, IsQuasiExcellentAdicFormalScheme (X.restrict (U i).isOpenEmbedding)) ∧
    ((∀ i, IsAdicFormalAffineOpen X (U i)) →
      (IsQuasiExcellentAdicFormalScheme X ↔
        ∀ i, IsQuasiExcellent (X.presheaf.obj (op (U i))))) := by
  sorry

/-- Reducedness and regularity can be checked on any formal open cover, and on the chart
rings of any cover by formal affine opens.
Source: Temkin §2.4.9 (blueprint: lem-per-qe-formal-regularity-locality).

Proof: Formal affine restrictions are regular by completing the identity and applying
regularMorphism_formalCompletion. Reducedness ascends along regular maps, and descends by
the sheaf axiom. Regularity ascends along flat maps with regular fibres. For descent,
choose a common principal neighbourhood of each maximal ideal in an arbitrary chart;
principal refinement supplies a faithfully flat local map to a localization of a regular
covering chart. Flat-under-regular descends regularity to the original maximal localization.
Localization then gives regularity at every prime. For a cover by formal affines, ascent
along the restrictions to the covering charts reduces both chart criteria to the open-cover
criteria. This includes the empty formal scheme. -/
theorem qeFormal_reduced_regular_cover_iff (X : RingedSpace.{u})
    (_hX : IsNoetherianAdicFormalScheme X)
    (_qX : X ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace)
    (_hqe : IsQuasiExcellentAdicFormalScheme X)
    (ι : Type v) (U : ι → Opens X) (_hU : (⨆ i, U i) = ⊤) :
    (IsReducedAdicFormalScheme X ↔
      ∀ i, IsReducedAdicFormalScheme (X.restrict (U i).isOpenEmbedding)) ∧
    ((∀ V : Opens X, IsAdicFormalAffineOpen X V →
        IsRegularRing (X.presheaf.obj (op V))) ↔
      ∀ (i : ι) (V : Opens (X.restrict (U i).isOpenEmbedding)),
        IsAdicFormalAffineOpen (X.restrict (U i).isOpenEmbedding) V →
          IsRegularRing ((X.restrict (U i).isOpenEmbedding).presheaf.obj (op V))) ∧
    ((∀ i, IsAdicFormalAffineOpen X (U i)) →
      (IsReducedAdicFormalScheme X ↔ ∀ i, _root_.IsReduced (X.presheaf.obj (op (U i)))) ∧
      ((∀ V : Opens X, IsAdicFormalAffineOpen X V →
          IsRegularRing (X.presheaf.obj (op V))) ↔
        ∀ i, IsRegularRing (X.presheaf.obj (op (U i))))) := by
  sorry

/-- Formal affine restrictions are regular and extend the actual singular ideals.
Source: Temkin §§2.4.9, 2.4.12, Lemma 2.4.6
(blueprint: lem-per-qe-formal-regularity-locality).

Proof: Complete the identity of Spec of the quasi-excellent target ring and apply the
regular-completion theorem to the smaller formal affine. For each prime upstairs,
flat-under-regular and flat-over-regular with regular closed fibre identify regularity
with regularity at its contracted prime. J-2 makes both nonregular loci closed.
Base change the regular map by the quotient by the radical singular ideal. The quotient
upstairs is reduced by regular-map reduced ascent, so the extended ideal is radical.
Equality of zero loci and the radical-ideal criterion give equality of the ideals. -/
theorem qeFormal_affine_restriction (X : RingedSpace.{u})
    (_hX : IsNoetherianAdicFormalScheme X)
    (_qX : X ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace)
    (_hqe : IsQuasiExcellentAdicFormalScheme X)
    (U V : Opens X) (_hU : IsAdicFormalAffineOpen X U)
    (_hV : IsAdicFormalAffineOpen X V) (e : V ≤ U) :
    (X.presheaf.map (homOfLE e).op).hom.IsRegular ∧
    Ideal.map (X.presheaf.map (homOfLE e).op).hom
        (absoluteSingularIdeal (X.presheaf.obj (op U))) =
      absoluteSingularIdeal (X.presheaf.obj (op V)) := by
  sorry

/-- The completed chart singular ideals glue uniquely to a coherent formal ideal.
Source: Temkin §2.4.9 (blueprint: lem-per-qe-formal-regularity-locality).

Proof: The radical nonregular ideal of every chart is finite by Noetherianity.
On a principal refinement, completion is exact on finite modules: completing a finite
presentation of the ideal identifies its completed image with the extended ideal.
The affine-restriction assertion identifies that image with the singular ideal of the
smaller chart. Common principal refinements identify the ideal subsheaves on overlaps.
Sections whose restrictions belong to these ideals form the global ideal subsheaf.
The sheaf axiom proves uniqueness; its local finite presentations prove coherence. -/
theorem qeFormal_singularIdeal_gluing (X : RingedSpace.{u})
    (_hX : IsNoetherianAdicFormalScheme X)
    (_qX : X ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace)
    (_hqe : IsQuasiExcellentAdicFormalScheme X) :
    ∃! J : FormalIdeal X, J.IsCoherent ∧
      ∀ (U : Opens X) (A : CommRingCat.{u}) (K : Ideal A),
        IsNoetherianRing A → IsAdicComplete K A →
        ∀ e : X.restrict U.isOpenEmbedding ≅ AdicFormalCompletion.formalSpectrum A K,
          J.comap (e.inv ≫ X.ofRestrict U.isOpenEmbedding) =
            completedFormalIdeal (Spec A) (affineFormalIdeal A K)
              (affineFormalIdeal A (absoluteSingularIdeal A)) := by
  sorry

/-- A formal morphism is regular exactly when it has regular covering chart maps.
Locality is pointwise on both source and target; no finite-type or adicity condition is imposed.
Source: Temkin §2.4.12, Lemma 2.4.6
(blueprint: lem-per-qe-formal-regularity-locality).

Proof: The forward implication chooses compatible affine neighbourhoods. Conversely, first
apply the regular-completion theorem inside each regular covering pair, replacing the target
ideal by a power when necessary for continuity. At a maximal ideal of an arbitrary source
chart choose common principal refinements of both this pair and a regular covering pair.
Compose their regular ring maps. Principal refinement supplies a faithfully flat local map
over the maximal ideal. The prime/maximal regular-map criterion and regular-permanence
descend regularity to the desired local map, and the same criterion gives the whole chart
map. Local stalk maps express that f is a morphism of formal schemes, rather than an
arbitrary morphism of ringed spaces. For Noetherian complete charts these maps are continuous:
images of an ideal of definition lie in the radical of any source ideal of definition,
as seen at all formal points; finite generation then gives the required power containment. -/
theorem qeFormal_regularity_locality {X Y : RingedSpace.{u}}
    (_hX : IsNoetherianAdicFormalScheme X) (_hY : IsNoetherianAdicFormalScheme Y)
    (_qX : X ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace)
    (_qY : Y ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace)
    (_hqeX : IsQuasiExcellentAdicFormalScheme X)
    (_hqeY : IsQuasiExcellentAdicFormalScheme Y)
    (f : Y ⟶ X) (_hf : ∀ y : Y, IsLocalHom (f.hom.stalkMap y).hom) :
    IsRegularOnAdicFormalAffines f ↔
      ∀ y : Y, ∃ (U : Opens X) (V : Opens Y),
        f.hom.base y ∈ U ∧ y ∈ V ∧
        IsAdicFormalAffineOpen X U ∧ IsAdicFormalAffineOpen Y V ∧
        ∃ e : V ≤ (Opens.map f.hom.base).obj U, (adicFormalAppLE f U V e).hom.IsRegular := by
  sorry

/-- Open immersions of quasi-excellent formal schemes are regular.
Source: Temkin §2.4.12, Lemma 2.4.6
(blueprint: lem-per-qe-formal-regularity-locality).

Proof: Locally identify the open immersion with a formal affine restriction. Such restrictions
are regular by the regular-completion theorem for the identity. Apply regularity locality
on both source and target to pass from these charts to every compatible affine pair. -/
theorem qeFormal_openImmersion_regular {X Y : RingedSpace.{u}}
    (_hX : IsNoetherianAdicFormalScheme X) (_hY : IsNoetherianAdicFormalScheme Y)
    (_qX : X ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace)
    (_qY : Y ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace)
    (_hqeX : IsQuasiExcellentAdicFormalScheme X)
    (_hqeY : IsQuasiExcellentAdicFormalScheme Y)
    (f : Y ⟶ X) (_hf : SheafedSpace.IsOpenImmersion f) :
    IsRegularOnAdicFormalAffines f := by
  sorry

/-- Composites of regular formal morphisms are regular.
Source: Temkin §2.4.12 (blueprint: lem-per-qe-formal-regularity-locality).

Proof: Choose compatible successive affine neighbourhoods about a source point. Locality
makes both chart maps regular. Compose regular ring maps; their composite fibre rings are
localizations of quotients of the Noetherian source chart ring, hence Noetherian. Locality
then implies regularity on every affine pair of the composite. -/
theorem qeFormal_regular_comp {X Y Z : RingedSpace.{u}}
    (_hX : IsNoetherianAdicFormalScheme X) (_hY : IsNoetherianAdicFormalScheme Y)
    (_hZ : IsNoetherianAdicFormalScheme Z)
    (_qX : X ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace)
    (_qY : Y ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace)
    (_qZ : Z ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace)
    (_hqeX : IsQuasiExcellentAdicFormalScheme X)
    (_hqeY : IsQuasiExcellentAdicFormalScheme Y)
    (_hqeZ : IsQuasiExcellentAdicFormalScheme Z)
    (f : Y ⟶ X) (g : Z ⟶ Y)
    (_hf : ∀ y : Y, IsLocalHom (f.hom.stalkMap y).hom)
    (_hg : ∀ z : Z, IsLocalHom (g.hom.stalkMap z).hom)
    (_hfr : IsRegularOnAdicFormalAffines f) (_hgr : IsRegularOnAdicFormalAffines g) :
    IsRegularOnAdicFormalAffines (g ≫ f) := by
  sorry

/-- Finite disjoint unions of regular formal morphisms are regular, including the empty union.
The open embeddings and their disjoint covering images specify the actual two unions.
Source: Temkin §2.4.12 (blueprint: lem-per-qe-formal-regularity-locality).

Proof: Take the union of the regular covering chart pairs of the component morphisms.
Their compatibility with f identifies these with chart pairs of the union. These pairs
cover the source and regularity locality gives the assertion. The empty covering proves
the assertion when the source and target are empty. -/
theorem qeFormal_regular_finite_disjoint_union {X Y : RingedSpace.{u}}
    (_hX : IsNoetherianAdicFormalScheme X) (_hY : IsNoetherianAdicFormalScheme Y)
    (_qX : X ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace)
    (_qY : Y ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace)
    (_hqeX : IsQuasiExcellentAdicFormalScheme X)
    (_hqeY : IsQuasiExcellentAdicFormalScheme Y)
    (f : Y ⟶ X) (_hf : ∀ y : Y, IsLocalHom (f.hom.stalkMap y).hom)
    (n : ℕ) (A B : Fin n → RingedSpace.{u})
    (a : ∀ i, A i ⟶ X) (b : ∀ i, B i ⟶ Y) (g : ∀ i, B i ⟶ A i)
    (_ha : ∀ i, SheafedSpace.IsOpenImmersion (a i))
    (_hb : ∀ i, SheafedSpace.IsOpenImmersion (b i))
    (_haCover : ∀ x : X, ∃ (i : Fin n) (z : A i), (a i).hom.base z = x)
    (_hbCover : ∀ y : Y, ∃ (i : Fin n) (z : B i), (b i).hom.base z = y)
    (_haDisjoint : ∀ i j, i ≠ j →
      Disjoint (Set.range (a i).hom.base) (Set.range (a j).hom.base))
    (_hbDisjoint : ∀ i j, i ≠ j →
      Disjoint (Set.range (b i).hom.base) (Set.range (b j).hom.base))
    (_hcomm : ∀ i, b i ≫ f = g i ≫ a i)
    (_hg : ∀ i, IsRegularOnAdicFormalAffines (g i)) :
    IsRegularOnAdicFormalAffines f := by
  sorry

/-- Every formal open subpair preserves the reduced, quasi-excellent, locally principal,
rig-regular properties; a quasi-compact open preserves a finite-type reduced closed fibre.
Source: Temkin §§2.4.9, 2.4.11, 3.1.1, 3.1.4
(blueprint: lem-per-qe-formal-regularity-locality).

Proof: Refine the open by formal principal charts. Restriction rings are Noetherian and
quasi-excellent, and reducedness follows by regular-map ascent. Flatness preserves the
injection given by multiplication by a regular generator of the distinguished ideal;
thus its extension is still locally principal and invertible, and defines the restricted
adic topology. Compatibility of the actual singular ideals preserves the containment of
a positive power of the distinguished ideal in the singular ideal. Each original chart
has Noetherian underlying space, so every open is quasi-compact and a finite subcover of
the principal charts exists. The reduced closed fibre restricts to the corresponding
open subscheme. For a quasi-compact open, choose finitely many ordinary principal charts
inside a finite affine cover of that fibre. Their coordinate rings remain finite-type
algebras over the same characteristic-zero field, so the restricted fibre is finite type.
The empty open has the empty atlas and empty reduced fibre. -/
theorem qeFormal_open_subpair (X : NoetherianAdicFormalScheme.{u})
    (_qX : X.space ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace)
    (_hqe : IsQuasiExcellentAdicFormalScheme X.space)
    (_hred : IsReducedAdicFormalScheme X.space) (_hinv : X.ideal.IsInvertible)
    (_hrig : ∀ c : FormalAffineChart X.space X.ideal,
      ∃ n : ℕ, 0 < n ∧ c.ideal ^ n ≤ absoluteSingularIdeal c.ring)
    (U : Opens X.space) :
    ∃ (Y : NoetherianAdicFormalScheme.{u})
      (e : Y.space ≅ X.space.restrict U.isOpenEmbedding),
      Y.ideal = X.ideal.comap (e.hom ≫ X.space.ofRestrict U.isOpenEmbedding) ∧
      IsReducedAdicFormalScheme Y.space ∧ IsQuasiExcellentAdicFormalScheme Y.space ∧
      Y.ideal.IsInvertible ∧
      (∀ c : FormalAffineChart Y.space Y.ideal,
        ∃ n : ℕ, 0 < n ∧ c.ideal ^ n ≤ absoluteSingularIdeal c.ring) ∧
      (IsCompact (U : Set X.space) → HasFormalVarietyClosedFibre X.space X.ideal →
        HasFormalVarietyClosedFibre Y.space Y.ideal) := by
  sorry

end AlgebraicGeometry
