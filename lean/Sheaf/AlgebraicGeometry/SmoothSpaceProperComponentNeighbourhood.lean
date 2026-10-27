/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import Sheaf.Paper.StrictHenselizationPointedMap
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.SpaceSmoothReducedLocality

/-! # A proper smooth fibre component over an étale neighbourhood

Source: Stacks Project, More on Morphisms of Spaces, Tags 0CWI and 0E1E;
Limits of Spaces, Tags 0827 and 08K1 (assembled étale-neighbourhood consequence)
(blueprint: lem-sfb-smooth-space-proper-component-neighbourhood).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The actual Yoneda map of an S-scheme morphism, viewed as an algebraic-space map.
Source: Stacks, Spaces, Tag 025Y; used in the base changes of Tags 0CWI and 0827
(blueprint: lem-sfb-smooth-space-proper-component-neighbourhood). -/
def smoothComponentSchemeMap {S : Scheme.{u}} {U V : Over S} (g : U ⟶ V) :
    schemeSpace U ⟶ schemeSpace V :=
  ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g)

/-- The structural map of an S-scheme, with its source explicitly fixed.
Source: Stacks, Spaces, Tag 025Y; base maps in Tags 0CWI and 0827
(blueprint: lem-sfb-smooth-space-proper-component-neighbourhood). -/
def smoothComponentBaseMap {S T : Scheme.{u}} (t : T ⟶ S) :
    schemeSpace (Over.mk t) ⟶ schemeSpace (Over.mk (𝟙 S)) :=
  smoothComponentSchemeMap (Over.homMk t (Category.comp_id t))

/-- A field-spectrum test (or any scheme test) over an S-scheme, with the composite base.
Source: Stacks, Spaces, Tag 025Y; geometric fibres in Tag 0E1E
(blueprint: lem-sfb-smooth-space-proper-component-neighbourhood). -/
def smoothComponentTestMap {S T U : Scheme.{u}} (t : T ⟶ S) (a : U ⟶ T) :
    schemeSpace (Over.mk (a ≫ t)) ⟶ schemeSpace (Over.mk t) :=
  smoothComponentSchemeMap (Over.homMk a rfl)

/-- The second projection of the existing sheaf fibre product, with its actual data.
Source: Stacks, Spaces, Tag 04T9, used in the fibre identifications of Tags 0CWI and 0827
(blueprint: lem-sfb-smooth-space-proper-component-neighbourhood). -/
def smoothComponentFibreSnd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) : enlargedFibreProduct f g ⟶ Y :=
  ObjectProperty.homMk (Limits.pullback.snd f.hom g.hom)

/-- A nonempty proper connected component of a smooth geometric fibre spreads to a
proper smooth finitely presented open family with nonempty geometrically connected fibres.
The isomorphism `eC` merely supplies an algebraic-space model of the given open subfunctor.
The final pullback square identifies the prescribed fibre as an open subspace of `X_s`.
Source: Stacks, More on Morphisms of Spaces, Tags 0CWI and 0E1E;
Limits of Spaces, Tags 0827 and 08K1 (assembled consequence)
(blueprint: lem-sfb-smooth-space-proper-component-neighbourhood).

Proof:
1. Restrict to an affine neighbourhood of s. Finitely many quasi-compact open atlas
   images cover C, giving a quasi-compact open U in X, without assuming X quasi-compact
   (lem-a1-space-etale-open-image, lem-a1-space-point-open-calculus).
2. Restriction preserves smoothness, local finite presentation and separatedness.
   The diagonal and product criteria make U finitely presented over this affine base
   (lem-sfb-space-separated-fp-composition, lem-sfb-space-qcqs-source-products,
   lem-sfb-scheme-etale-source-target-properties).
3. Take the pointed strict henselization A with separably closed residue field K inside
   Ω (def-weil-pbc-strict-henselization-limit,
   lem-weil-pbc-strict-henselization-local-structure,
   lem-weil-pbc-strict-henselization-pointed-map,
   def-weil-pbc-relative-separable-closure). The pointed equations retain the given s.
4. Descend C to a clopen component D over K using
   lem-sfb-space-sepclosed-components-base-change. It is quasi-compact and finite type;
   descend universal closedness by lem-sfb-space-fpqc-descend-universally-closed.
   Thus D is proper, without requiring Ω/K finitely presented.
5. Apply lem-sfb-space-henselian-proper-clopen-lift to obtain a proper clopen W over A
   with geometric fibre C, using def-weil-pbc-henselian-terminology and
   lem-sfb-space-flat-proper-fp-locality.
6. Reindex the affine pointed neighbourhoods by a small directed set
   (lem-weil-pbc-cofiltered-limit-directed-reindex). The spaces U_i are qcqs by
   lem-sfb-space-fp-qcqs-source and have affine transitions; their limit is U_A by
   lem-sfb-space-affine-limits-schematic-stages.
7. Descend the quasi-compact open W by lem-sfb-space-limit-open-cover-descent.
   The descended open is finitely presented by the diagonal/product argument in step 2.
   Apply lem-sfb-space-eventually-proper to make it proper at a later stage. The pointed
   equations give its fibre C.
8. It is smooth by lem-sfb-space-smooth-surjective-fppf-locality; smooth charts are flat
   by lem-pc-smooth-flat and lem-sfb-space-local-properties-chart-test, and geometric
   fibres are reduced by lem-sfb-space-smooth-reduced-locality. Apply
   lem-sfb-space-proper-flat-geometric-component-count: the count is one at the given
   point, so shrink the base to the open locus where every fibre has one component.
9. The given lift factors through this open. Étaleness persists by
   lem-sfb-scheme-etale-source-target-properties. Base change preserves properness,
   finite presentation and smoothness (lem-sfb-space-flat-proper-fp-locality,
   lem-sfb-space-smooth-surjective-fppf-locality). The fibre is C with its open structure. -/
theorem exists_proper_smooth_component_neighbourhood
    {S : Scheme.{u}} [IsLocallyNoetherian S] (X : AlgebraicSpace S)
    (f : X ⟶ schemeSpace (Over.mk (𝟙 S)))
    (hf_sep : MapIsSeparated f) (hf_sm : MapIsLocally (@Smooth) f)
    (hf_lfp : MapIsLocallyOfFinitePresentation f)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (Copen : OpenSubspace (enlargedFibreProduct f
      (smoothComponentBaseMap s)))
    (C : AlgebraicSpace S) (eC : C.obj.obj ≅ Copen.val.toFunctor)
    (iC : C ⟶ enlargedFibreProduct f (smoothComponentBaseMap s))
    (hiC : iC.hom.hom = eC.hom ≫ Copen.val.ι)
    (hC : ∃ c : Point (enlargedFibreProduct f
      (smoothComponentBaseMap s)).obj.obj,
      pointImage Copen.val.ι = connectedComponent c)
    (hC_proper : MapIsProper
      (iC ≫ smoothComponentFibreSnd f (smoothComponentBaseMap s))) :
    ∃ (T : Scheme.{u}) (t : T ⟶ S) (_ : Etale t)
      (st : Spec (.of Ω) ⟶ T) (hst : st ≫ t = s)
      (Vopen : OpenSubspace (enlargedFibreProduct f
        (smoothComponentBaseMap t)))
      (V : AlgebraicSpace S) (eV : V.obj.obj ≅ Vopen.val.toFunctor)
      (iV : V ⟶ enlargedFibreProduct f (smoothComponentBaseMap t)),
      iV.hom.hom = eV.hom ≫ Vopen.val.ι ∧
      ∃ p : V ⟶ schemeSpace (Over.mk t),
        p = iV ≫ smoothComponentFibreSnd f (smoothComponentBaseMap t) ∧
        MapIsProper p ∧ MapIsLocally (@Smooth) p ∧
        MapIsLocallyOfFinitePresentation p ∧ MapIsQuasiCompact p.hom.hom ∧
        MapIsQuasiCompact (Limits.pullback.diagonal p.hom.hom) ∧
        (∀ (K : Type u) [Field K] (z : Spec (.of K) ⟶ T)
          (L : Type u) [Field L] [Algebra K L],
          ConnectedSpace (Point (enlargedFibreProduct p
            (smoothComponentTestMap t
              (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ z))).obj.obj)) ∧
        ∃ k : C ⟶ V,
          k.hom.hom ≫ iV.hom.hom ≫
              (Limits.pullback.fst f.hom
                (smoothComponentBaseMap t).hom).hom =
            iC.hom.hom ≫ (Limits.pullback.fst f.hom
              (smoothComponentBaseMap s).hom).hom ∧
          IsPullback k
            (iC ≫ smoothComponentFibreSnd f (smoothComponentBaseMap s))
            p (smoothComponentSchemeMap (Over.homMk st hst)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
