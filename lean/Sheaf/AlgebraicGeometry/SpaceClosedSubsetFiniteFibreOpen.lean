module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The finite-fibre locus of a closed subset of a proper algebraic space

Source: Stacks Project, More on Morphisms of Spaces, Tag 0A4Y
(lemma-proper-finite-fibre-finite-in-neighbourhood); Properties of Spaces, Tag 03IQ;
Decent Spaces, Tag 0ACK
(blueprint: lem-sfb-space-closed-subset-finite-fibre-open).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inverse image of a subset in the actual fibre product along a scheme map.
This is a set of points of the fibre product, not a set of rational lifts: the classes of
field-valued representatives whose image under the first projection has class in `T`.
Source: Stacks, Tags 03IQ and 03H4
(blueprint: lem-sfb-space-closed-subset-finite-fibre-open). -/
def closedSupportFibre {B : Scheme.{u}} {F : (Over B)ᵒᵖ ⥤ Type u} {S U : Over B}
    (f : F ⟶ yoneda.obj S) (T : Set (Point F)) (a : U ⟶ S) :
    Set (Point (Limits.pullback f (yoneda.map a))) :=
  {q | ∃ p : PointRepresentative (Limits.pullback f (yoneda.map a)),
    (Quot.mk _ p : Point (Limits.pullback f (yoneda.map a))) = q ∧
      (Quot.mk _ (p.map (Limits.pullback.fst f (yoneda.map a))) : Point F) ∈ T}

/-- The canonical field-valued point over a scheme point after a residue-field extension.
The map to the ambient base is the composite with the structure map of `S`.
Source: Stacks, Tag 0ACK, field-valued representative of a point
(blueprint: lem-sfb-space-closed-subset-finite-fibre-open). -/
def supportResidueFieldPoint {B : Scheme.{u}} (S : Over B) (s : S.left)
    (K : Type u) [Field K] [Algebra (S.left.residueField s) K] :
    Over.mk ((Spec.map (CommRingCat.ofHom (algebraMap (S.left.residueField s) K)) ≫
      S.left.fromSpecResidueField s) ≫ S.hom) ⟶ S :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (S.left.residueField s) K)) ≫
    S.left.fromSpecResidueField s) rfl

/-- The set where the inverse image of `T` in the geometric fibre is finite, using the
chosen algebraic closure of the residue field. Openness is a theorem, not part of the data.
Source: Stacks, Tags 0A4Y, 03IQ and 0ACK
(blueprint: lem-sfb-space-closed-subset-finite-fibre-open). -/
def closedSupportFiniteFibreLocus {B : Scheme.{u}} {F : (Over B)ᵒᵖ ⥤ Type u}
    {S : Over B} (f : F ⟶ yoneda.obj S) (T : Set (Point F)) : Set S.left :=
  {s | (closedSupportFibre f T
    (supportResidueFieldPoint S s (AlgebraicClosure (S.left.residueField s)))).Finite}

/-- For a proper algebraic space over a scheme and a closed subset of its point space,
its finite geometric-fibre locus is open, commutes with arbitrary scheme base change,
and can be tested after every field extension of a residue field, including itself.

Source: Stacks, Tag 0A4Y (lemma-proper-finite-fibre-finite-in-neighbourhood),
Tag 03IQ (lemma-reduced-closed-subspace), and Tag 0ACK
(lemma-conditions-on-fibre-and-qf)
(blueprint: lem-sfb-space-closed-subset-finite-fibre-open).

Proof:
1. By lem-sfb-space-reduced-closed-support give T its reduced closed subspace Z.
The closed immersion Z -> X is proper by lem-sfb-space-closed-subspace-proper;
lem-sfb-space-proper-composition makes Z -> S proper, hence separated and finite type.
2. By lem-trf-space-fibre-products-etale-covers the sheaf fibre products are algebraic
spaces with their categorical universal property. The support theorem identifies the
points of Z_K with the inverse image of T in X_K. The criterion
lem-sfb-space-finite-fibre-quasifinite-criterion says these are finite exactly when
Z -> S is quasi-finite at all points above s.
3. By lem-sfb-space-quasifinite-locus-open its quasi-finite locus Q is open. Properness
makes the image of Z minus Q closed. Its complement V is therefore open, and s lies in V
exactly when all points above s are quasi-finite. Step 2 identifies V with the stated locus.
4. Empty fibres impose a vacuous condition on all their points. Thus the construction
includes both empty T and empty fibres, without any nonemptiness assumption.
5. The criterion in step 2 is independent of the representative field extension K.
It gives the field-extension equivalence, also for the residue field and any algebraic
closure; no equality of the numbers of ordinary and geometric points is claimed.
6. For g:S' -> S, lem-sfb-space-proper-base-change makes X times_S S' proper over S'.
The support theorem identifies the pulled-back subset with the support of Z times_S S'.
For s' over s, an algebraic closure L of kappa(s') is also an extension of kappa(s).
Fibre-product uniqueness identifies (X times_S S')_L with X_L compatibly with T.
Step 5 therefore identifies membership in the two loci, giving the stated equality.
No compatibility of reduced structures with base change is needed.
-/
theorem isOpen_closedSupportFiniteFibreLocus {B : Scheme.{u}} (S : Over B)
    (X : AlgebraicSpace B) (f : X ⟶ schemeSpace S) (hf : MapIsProper f)
    (T : Set (Point X.obj.obj)) (hT : IsClosed T) :
    IsOpen (closedSupportFiniteFibreLocus f.hom.hom T) ∧
      (∀ (S' : Over B) (g : S' ⟶ S),
        closedSupportFiniteFibreLocus (Limits.pullback.snd f.hom.hom (yoneda.map g))
          (closedSupportFibre f.hom.hom T g) =
            g.left ⁻¹' closedSupportFiniteFibreLocus f.hom.hom T) ∧
      ∀ (s : S.left) (K : Type u) [Field K] [Algebra (S.left.residueField s) K],
        s ∈ closedSupportFiniteFibreLocus f.hom.hom T ↔
          (closedSupportFibre f.hom.hom T (supportResidueFieldPoint S s K)).Finite := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
