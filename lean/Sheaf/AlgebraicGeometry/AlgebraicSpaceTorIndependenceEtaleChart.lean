module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorComparison
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests

/-! # Geometric Tor independence and étale scheme charts

Source: Stacks Project, spaces-perfect.tex, Tags 08IP and 08IQ.
(blueprint: lem-sfb-space-tor-independence-etale-chart-criterion).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Geometric Tor independence uses the actual geometric structure-sheaf stalks and their
canonical germ maps, transporting the common target stalk along the equality of points.
The two modules are the rings themselves with scalars restricted by these maps.
Source: Stacks Project, Tag 08IP
(blueprint: lem-sfb-space-tor-independence-etale-chart-criterion). -/
def IsGeometricallyTorIndependent {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    (f : F ⟶ H) (g : G ⟶ H) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ F.obj.obj)
    (y : yoneda.obj (Over.mk s) ⟶ G.obj.obj)
    (h : x ≫ f.hom.hom = y ≫ g.hom.hom) (i : ℕ), 0 < i →
    IsZero (((CategoryTheory.Tor' (ModuleCat.{u}
      (SingleComplex.stalkRing s (x ≫ f.hom.hom))) i).obj
        ((ModuleCat.restrictScalars (SingleComplex.stalkMap f s x)).obj
          (ModuleCat.of (SingleComplex.stalkRing s x) (SingleComplex.stalkRing s x)))).obj
        ((ModuleCat.restrictScalars
          ((SingleComplex.stalkMap g s y).comp
            (eqToHom (congrArg (fun z ↦ SingleComplex.stalkRing s z) h)).hom)).obj
          (ModuleCat.of (SingleComplex.stalkRing s y) (SingleComplex.stalkRing s y))))

/-- For every choice of the three surjective étale scheme atlases, geometric Tor
independence is equivalent to ordinary local-ring Tor independence of the chart maps.
The atlas maps to the two fibre products are the canonical pullback lifts.
Source: Stacks Project, Tag 08IQ, equivalence (1) and (4)
(blueprint: lem-sfb-space-tor-independence-etale-chart-criterion).
Proof: (1) Specialize the flat-ring-diagram cohomology comparison to A[0] and degree -i
[lem-sfb-flat-ring-diagram-tensor-cohomology], obtaining the Tor base-change formula.
(2) For schemes identify geometric local rings with strict henselizations
[lem-sfb-space-strict-local-flatness]. Functoriality and strict-local refinement give
flatness of the two maps after strict base change; faithful flatness of strict
henselization and the formula prove ordinary-to-geometric vanishing.
(3) Conversely work on affine opens. Localizing both factors and the base identifies
localized Tor with scalar extension of affine Tor. For every prime of the tensor ring,
choose an algebraic closure of its residue field and the corresponding compatible
geometric points. Functoriality gives a map from the tensor of geometric stalks to the
strict henselization of this tensor-ring localization. Geometric vanishing and faithful
flatness imply that affine Tor vanishes at every prime, hence vanishes.
(4) Affine neighbourhoods inside the inverse image of an affine base neighbourhood
then give vanishing for every ordinary pair of points; no affine intersection is needed.
(5) Étale maps identify geometric local rings and their maps. Lift any pair of geometric
points first to W and then to U and V, over the original algebraically closed field
[lem-sfb-etale-geometric-point-specified-lift]. Surjectivity and the fibre-product
property supply these lifts with a common W-image. Thus geometric vanishing descends
and ascends along the three atlases. Apply the scheme equivalence from (2)--(4).
(6) The atlases were arbitrary, so the equivalence holds for every such choice; taking
identities gives the scheme comparison below. None of these arguments needs flatness,
quasi-compactness, separation, or finiteness of the original maps or spaces. -/
theorem torIndependent_iff_etale_chart {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    (f : F ⟶ H) (g : G ⟶ H) (U V W : Over S)
    (a : yoneda.obj W ⟶ H.obj.obj) (b : yoneda.obj U ⟶ F.obj.obj)
    (c : yoneda.obj V ⟶ G.obj.obj) (p : U ⟶ W) (q : V ⟶ W)
    (hb : b ≫ f.hom.hom = yoneda.map p ≫ a)
    (hc : c ≫ g.hom.hom = yoneda.map q ≫ a)
    (hae : IsEtale a) (has : IsSurjective a)
    (hbe : IsEtale (Limits.pullback.lift b (yoneda.map p) hb))
    (hbs : IsSurjective (Limits.pullback.lift b (yoneda.map p) hb))
    (hce : IsEtale (Limits.pullback.lift c (yoneda.map q) hc))
    (hcs : IsSurjective (Limits.pullback.lift c (yoneda.map q) hc)) :
    IsGeometricallyTorIndependent f g ↔ PullbackStalkTensor.IsTorIndependent p.left q.left :=
  by sorry

/-- For representable algebraic spaces the geometric condition agrees with the ordinary
local-ring condition on the representing schemes. Isomorphisms of presheaves specify
exactly the scheme presentations and the two compatibility equations specify the maps.
Source: Stacks Project, Tag 08IQ, scheme comparison in the proof
(blueprint: lem-sfb-space-tor-independence-etale-chart-criterion).
Proof: use the preceding arbitrary-atlas criterion with the three scheme presentations
and the identity atlases. Isomorphisms are surjective étale; their pullbacks are so too
[lem-trf-space-representable-etale-scheme-tests]. The resulting ordinary condition is
exactly the condition for the two given representing scheme maps. -/
theorem torIndependent_iff_scheme_local {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    (f : F ⟶ H) (g : G ⟶ H) (U V W : Over S)
    (eF : yoneda.obj U ≅ F.obj.obj) (eG : yoneda.obj V ≅ G.obj.obj)
    (eH : yoneda.obj W ≅ H.obj.obj) (p : U ⟶ W) (q : V ⟶ W)
    (hp : eF.hom ≫ f.hom.hom = yoneda.map p ≫ eH.hom)
    (hq : eG.hom ≫ g.hom.hom = yoneda.map q ≫ eH.hom) :
    IsGeometricallyTorIndependent f g ↔ PullbackStalkTensor.IsTorIndependent p.left q.left :=
  by sorry

end AlgebraicGeometry.AlgebraicSpace
