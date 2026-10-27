module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Blowup.Affine.ChartAlgebra
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.RingHom.Flat

/-! # Group dilatations along a closed fibre

Source: Bosch–Lütkebohmert–Raynaud, Néron Models, §3.2, construction and Propositions 1–2,
printed pp.62–64, globalized over a Dedekind base as in §10.1, Proposition 4.
(blueprint: lem-sfb-group-dilatation-universal-property)

The auxiliary predicates spell out the smooth-test lifting and affine-chart clauses of
this single statement. Chart algebras reuse `AffineBlowup.chartRing`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The ideal of a closed centre on an affine chart: pull back the centre and take the
kernel of the restriction on sections, using Γ(Spec A) = A.
Source: BLR §3.2, construction, pp.62–63.
(blueprint: lem-sfb-group-dilatation-universal-property) -/
noncomputable def dilatationChartIdeal {G Z : Scheme.{u}} (z : Z ⟶ G)
    (A : CommRingCat.{u}) (j : Spec A ⟶ G) : Ideal A :=
  RingHom.ker (((Scheme.ΓSpecIso A).inv ≫ (pullback.snd z j).appTop).hom)

/-- The smooth-test universal property, with the fibre condition expressed by an actual
scheme-theoretic factorization through the centre, rather than a condition on points.
Source: BLR §3.2, Proposition 1(b), p.63, restricted to smooth test schemes.
(blueprint: lem-sfb-group-dilatation-universal-property) -/
def HasDilatationSmoothLifting {S T : Scheme.{u}} (t : T ⟶ S)
    {H G : Over S} (d : H ⟶ G) {Z : Scheme.{u}} (z : Z ⟶ G.left) : Prop :=
  ∀ (X : Over S) (_ : Smooth X.hom) (f : X ⟶ G),
    (∃ a : pullback X.hom t ⟶ Z,
      a ≫ z = pullback.fst X.hom t ≫ f.left) →
    ∃! f' : X ⟶ H, f' ≫ d = f

/-- The affine description of a dilatation over an affine base with distinguished ideal m.
Every affine base neighbourhood on which m = (π), and every affine chart above it, has
inverse image Spec A[I/π]. The equation for its projection specifies the canonical map.
Quantification over every such neighbourhood and every generator includes independence
of charts and of the local generator.
Source: BLR §3.2, construction, pp.62–63.
(blueprint: lem-sfb-group-dilatation-universal-property) -/
def HasDilatationAffineCharts (D : CommRingCat.{u}) (m : Ideal D)
    {H G : Over (Spec D)} (d : H ⟶ G) {Z : Scheme.{u}} (z : Z ⟶ G.left) : Prop :=
  ∀ (B : CommRingCat.{u}) (r : D ⟶ B) (_ : IsOpenImmersion (Spec.map r))
    (π : B) (_ : Ideal.map r.hom m = Ideal.span {π})
    (A : CommRingCat.{u}) (φ : B ⟶ A) (j : Spec A ⟶ G.left)
    (_ : IsOpenImmersion j) (_ : j ≫ G.hom = Spec.map φ ≫ Spec.map r),
    ∃ e : pullback d.left j ≅
        Spec (.of (AffineBlowup.chartRing (dilatationChartIdeal z A j) (φ.hom π))),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A
        (AffineBlowup.chartRing (dilatationChartIdeal z A j) (φ.hom π)))) =
          pullback.snd d.left j

/-- Dilatation of a closed subgroup of the closed fibre of a flat separated, locally finite
type group scheme over a one-dimensional Dedekind domain.

Source: BLR §3.2, Propositions 1–2, pp.63–64; Dedekind globalization as in §10.1,
Proposition 4, p.291. (blueprint: lem-sfb-group-dilatation-universal-property)

Proof plan (the eight steps of the DAG):
1. Use lem-sc-dedekind-localization-dvr and clear finitely many denominators to find a
   neighbourhood where the closed-point ideal is (π). The locally Noetherian and locally
   finite type nodes pqf-def-locnoeth, pqf-lem-locnoeth-lft and
   pqf-lem-affine-open-locnoeth make the chart rings Noetherian. Form A[I/π] using
   def-nagata-blowup-chart-ring.
2. For A → C carrying I into πC, with π injective on C, map x/πⁿ to the unique c with
   πⁿc = image(x). The normal-form and fraction-equality nodes
   lemma-nagata-chart-ring-normal-form and lemma-nagata-chart-ring-fraction-equality
   prove existence, independence of expression, and uniqueness of this ring map.
3. By lem-weil-pbc-flat-morphism-affine-criterion and def-weil-pbc-flat-ring-map, A is
   D-torsion-free. So are A[1/π] and its subring A[I/π]. Apply
   lem-sfb-dedekind-torsionfree-module-flat and lem-weil-pbc-flat-ring-map-iff-flat-affine.
   Finite generation of I gives local finite type; I A[I/π] = π A[I/π] gives the fibre map.
4. Cover an arbitrary flat test scheme by affine opens. Its rings are π-torsion-free by
   the flat affine criterion. Apply step 2 and glue with
   lem-weil-pbc-scheme-morphism-gluing. No quasi-compactness of the test is used.
5. On overlaps use the flat-test uniqueness to get inverse transition maps and the cocycle
   identity. Use lem-weil-pbc-glue-schemes and lem-weil-pbc-affine-opens-basis. The chart
   algebra becomes A[1/π] after inverting π, so glue with G outside the closed fibre.
6. By pqf-lem-affine-local-target and lem-weil-pbc-affine-morphism-permanence the map is
   affine and separated. Compose separated maps for separatedness over S. Use
   lem-pc-smooth-flat to restrict the flat-test property to smooth tests. Flatness and
   local finite type are checked on these open charts using
   lem-sfb-scheme-etale-source-target-properties and lem-weil-pbc-open-immersion-etale.
7. Flatness is preserved under base change and composition
   (lem-weil-pbc-flat-morphism-base-change, lem-pc-flat-compose), so the flat-test property
   applies to every finite power of G'. Lift multiplication, identity and inverse because
   F is a subgroup (def-sc-group-scheme). Uniqueness proves the group diagrams and the
   homomorphism condition, and preserves commutativity.
8. Replacing π by a unit multiple gives the same chart subalgebra. Flat-test uniqueness
   identifies different chart systems. Localizing at the closed-point prime preserves
   the subalgebra construction and its lifting calculation, giving the displayed local
   charts and lifting property over D_s. The chartwise construction never requires G or
   F to be quasi-compact. -/
theorem group_dilatation_universal_property
    (D : CommRingCat.{u}) [IsDedekindDomain D] (hD : ringKrullDim D = 1)
    (s : PrimeSpectrum D) (hs : IsClosed ({s} : Set (Spec D)))
    (G : Grp (Over (Spec D))) [Flat G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (F : Grp (Over (Spec (.of ((Spec D).residueField s)))))
    (i : F ⟶ (Over.pullback ((Spec D).fromSpecResidueField s)).mapGrp.obj G)
    [IsClosedImmersion i.hom.hom.left] :
    ∃ (H : Grp (Over (Spec D))) (d : H ⟶ G),
      Flat H.X.hom ∧ IsSeparated H.X.hom ∧ LocallyOfFiniteType H.X.hom ∧
      IsAffineHom d.hom.hom.left ∧
      IsIso ((Over.pullback
        (Scheme.Opens.ι (⟨{s}ᶜ, hs.isOpen_compl⟩ : (Spec D).Opens))).map d.hom.hom) ∧
      (∃ a : (Over.pullback ((Spec D).fromSpecResidueField s)).obj H.X ⟶ F.X,
        a ≫ i.hom.hom =
          (Over.pullback ((Spec D).fromSpecResidueField s)).map d.hom.hom) ∧
      HasDilatationSmoothLifting ((Spec D).fromSpecResidueField s) d.hom.hom
        (i.hom.hom.left ≫ pullback.fst G.X.hom ((Spec D).fromSpecResidueField s)) ∧
      (IsCommMonObj G.X → IsCommMonObj H.X) ∧
      HasDilatationAffineCharts D s.asIdeal d.hom.hom
        (i.hom.hom.left ≫ pullback.fst G.X.hom ((Spec D).fromSpecResidueField s)) ∧
      HasDilatationAffineCharts (.of (Localization.AtPrime s.asIdeal))
        (Ideal.map (algebraMap D (Localization.AtPrime s.asIdeal)) s.asIdeal)
        ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap D (Localization.AtPrime s.asIdeal))))).map d.hom.hom)
        (pullback.snd
          (i.hom.hom.left ≫ pullback.fst G.X.hom ((Spec D).fromSpecResidueField s))
          (pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom
            (algebraMap D (Localization.AtPrime s.asIdeal)))))) ∧
      HasDilatationSmoothLifting
        (pullback.snd ((Spec D).fromSpecResidueField s) (Spec.map (CommRingCat.ofHom
          (algebraMap D (Localization.AtPrime s.asIdeal)))))
        ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap D (Localization.AtPrime s.asIdeal))))).map d.hom.hom)
        (pullback.snd
          (i.hom.hom.left ≫ pullback.fst G.X.hom ((Spec D).fromSpecResidueField s))
          (pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom
            (algebraMap D (Localization.AtPrime s.asIdeal)))))) := by
  sorry

end AlgebraicGeometry
