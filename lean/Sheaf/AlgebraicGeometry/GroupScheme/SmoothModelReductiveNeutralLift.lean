module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.RingTheory.HenselianSmoothAlgebraLifting

/-! # Split reductive neutral model of a smooth affine group

Source: Prasad--Yu, On quasi-reductive group schemes, Lemma 3.5, Section 3.6,
and Proposition 4.3, first paragraph, printed pp.6--8.
(blueprint: lem-sfb-smooth-model-reductive-neutral-lift).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- The open union of the generic fibre and the special neutral component of a smooth
model is affine of finite type and split reductive when the latter component is reductive.
The fibre isomorphisms commute with the inclusions, so they identify the actual subschemes.

Source: Prasad--Yu, Lemma 3.5, Section 3.6, and Proposition 4.3, first paragraph,
printed pp.6--8; Conrad, Reductive group schemes, Propositions 3.1.6, 3.1.9 and B.3.4.
(blueprint: lem-sfb-smooth-model-reductive-neutral-lift).

Proof:
1. By lem-sfb-finite-type-group-identity-subgroup the special identity component H is
clopen. Remove its complement from N. The resulting open D has generic fibre N_L and
special fibre H. The group operations restrict to D: generically nothing was removed,
and on the special fibre H is a subgroup. The group diagrams descend through its mono.
2. Write N = Spec E and choose a uniformizer pi. The affine smoothness comparison
lem-weil-pbc-smooth-ring-map-iff-smooth-affine, smooth flatness
lem-weil-pbc-smooth-ring-map-flat and lem-trf-flat-module-torsionfree-domain give
E contained in E[1/pi]. By lem-weil-pbc-spec-clopen-idempotent choose an idempotent
abar on E/pi with H = V(abar) = D(1-abar). Lift it to a and write a(1-a) = pi b.
Then the required open is D(pi) union D(1-a).
3. Inside E[1/pi] put B = E[a/pi]. With t = a/pi, 1 = (1-a) + pi t, so the two
basic opens cover Spec B. Their rings are E[1/pi] and E[1/(1-a)], respectively:
on the latter t = b/(1-a), and pi-torsion-freeness justifies the localization.
By lem-weil-pbc-affine-open-section-vanishing-prime the chart maps and their overlap
identify Spec B with D. It is affine of finite type since only one generator was added.
4. By lem-pc-open-immersion-smooth-composition, D is smooth. Apply
lem-sfb-reductive-torus-fibre-openness at the closed point. Any open neighborhood of that
point in a local spectrum is the whole spectrum, since a basic open containing the
maximal ideal is defined by a unit. The geometric neutral fibres are therefore reductive.
The generic fibre is geometrically connected by hypothesis and H is connected, so all
geometric fibres themselves are reductive.
5. Choose a split maximal torus T0 in H using lem-sfb-reductive-borel-pair-structure.
By lem-sfb-split-torus-etale-subgroup-lift it lifts over an affine etale neighborhood U
of the closed point, with a residue-field point u. Etale implies smooth by
lem-weil-pbc-etale-smooth-zero-dimensional-fibres. The affine smoothness comparison and
lem-trf-henselian-smooth-algebra-lifting lift u to a section Spec R to U. Pull back the
torus inclusion along this section. Closed immersions remain closed under base change,
as a quotient of coordinate rings stays a quotient after tensoring.
6. Apply the maximality assertion of lem-sfb-reductive-torus-fibre-openness to this
lifted torus. It is maximal on a neighborhood of the closed point, hence everywhere by
the same local-spectrum argument. This includes rank zero. -/
theorem smoothModel_reductive_neutral_lift
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (L : Type u) [Field L] [Algebra R L] [IsFractionRing R L]
    (N : Grp (Over (Spec (.of R))))
    [Smooth N.X.hom] [IsAffine N.X.left]
    [LocallyOfFiniteType N.X.hom] [QuasiCompact N.X.hom]
    [GeometricallyConnected
      (pullback.snd N.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R L))))]
    (hH : ReductiveTorusCentralizer.IsReductive
      (Grp.mk ((@GrpObj.identityComponent (IsLocalRing.ResidueField R) inferInstance
          ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj N.X)
          inferInstance
          (inferInstanceAs (LocallyOfFiniteType (pullback.snd N.X.hom
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))))
          (inferInstanceAs (QuasiCompact (pullback.snd N.X.hom
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))))))))) :
    ∃ (D : Grp (Over (Spec (.of R)))) (i : D ⟶ N),
      IsOpenImmersion i.hom.hom.left ∧
      Set.range i.hom.hom.left =
        Set.range (pullback.fst N.X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap R L)))) ∪
        Set.range (((@GrpObj.identityComponentι (IsLocalRing.ResidueField R) inferInstance
          ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj N.X)
          inferInstance
          (inferInstanceAs (LocallyOfFiniteType (pullback.snd N.X.hom
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))))
          (inferInstanceAs (QuasiCompact (pullback.snd N.X.hom
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))))))).left ≫
          pullback.fst N.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ∧
      Smooth D.X.hom ∧ IsAffine D.X.left ∧
      LocallyOfFiniteType D.X.hom ∧ QuasiCompact D.X.hom ∧
      IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mapGrp.map i) ∧
      (∃ e : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj D.X ≅
          (@GrpObj.identityComponent (IsLocalRing.ResidueField R) inferInstance
          ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj N.X)
          inferInstance
          (inferInstanceAs (LocallyOfFiniteType (pullback.snd N.X.hom
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))))
          (inferInstanceAs (QuasiCompact (pullback.snd N.X.hom
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))))),
        e.hom ≫ (@GrpObj.identityComponentι (IsLocalRing.ResidueField R) inferInstance
          ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj N.X)
          inferInstance
          (inferInstanceAs (LocallyOfFiniteType (pullback.snd N.X.hom
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))))
          (inferInstanceAs (QuasiCompact (pullback.snd N.X.hom
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))))) =
        (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map
          i.hom.hom) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω),
        ReductiveTorusCentralizer.IsReductive
          ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).mapGrp.obj D)) ∧
      ∃ (r : ℕ) (j : RingGroupSchemes.splitTorus R r ⟶ D),
        IsClosedImmersion j.hom.hom.left ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω),
          ReductiveTorusCentralizer.IsMaximalTorus
            ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).mapGrp.map j) := by
  sorry

end AlgebraicGeometry
