module

public import Sheaf.AlgebraicGeometry.SmoothIntegralSpaceMap
public import Sheaf.AlgebraicGeometry.LocallyFiniteSpaceDivisors
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SpaceSmoothReducedLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import Sheaf.AlgebraicGeometry.AlgebraicSpaceLocalDimensionChartInvariance
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.RegularSpaceDivisorLineDictionary
import Sheaf.AlgebraicGeometry.RegularPrimeDivisorLocalEquations
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres

/-! # Vertical divisors for smooth maps with integral geometric fibres

Source: Stacks Project, Algebra, Tag 00ON; Descent, Tag 036D; Spaces Divisors,
Tags 0DMM and 0EPQ; Deligne, Le lemme de Gabber, Section 4.2, printed p.142
(blueprint: lem-sfb-smooth-integral-fibre-vertical-divisors).

All spaces are over Spec Z, so separatedness of a structure map is absolute
separatedness. A scheme base remains arbitrary. Divisor groups have locally finite,
rather than globally finite, coefficient support.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The geometric and normalized-divisor conclusions, for a specified additive
identification. Prime supports are actual reduced closed subspaces, and their actual
scheme-theoretic inverse images are reduced and irreducible. The singleton coefficient
formula includes multiplicity one and vanishing of every other coefficient.
Source: Stacks, Tags 00ON, 036D, 0AGA and 0EPQ; Deligne 4.2
(blueprint: lem-sfb-smooth-integral-fibre-vertical-divisors). -/
def VerticalDivisorIdentification
    {S : Scheme.{u}} {X B : AlgebraicSpace S} (p : X ⟶ B)
    (W : Set (Point B.obj.obj))
    (e : SupportedLocallyFiniteDivisors B W ≃+
      SupportedLocallyFiniteDivisors X (mapPoint p.hom.hom ⁻¹' W)) : Prop :=
  (∀ U : X.EtaleSite, IsRegularScheme (X.etaleForget.obj U)) ∧
    Dense (mapPoint p.hom.hom ⁻¹' W) ∧
    (∀ D : SupportedLocallyFiniteDivisors B W,
      ∃! C : SpaceCartierDivisor B, HasLocallyFiniteWeilDivisor B C D.val) ∧
    (∀ D : SupportedLocallyFiniteDivisors X (mapPoint p.hom.hom ⁻¹' W),
      ∃! C : SpaceCartierDivisor X, HasLocallyFiniteWeilDivisor X C D.val) ∧
    ∃ hp : MapIsFlat p,
      (∀ D, IsLocallyFiniteDivisorPullback p hp D.val (e D).val) ∧
      ∃ r : {z : SpacePrimeDivisor B // Disjoint (spacePrimeSupport B z) W} ≃
          {z : SpacePrimeDivisor X //
            Disjoint (spacePrimeSupport X z) (mapPoint p.hom.hom ⁻¹' W)},
        ∀ z,
          spacePrimeSupport X (r z).val =
            mapPoint p.hom.hom ⁻¹' spacePrimeSupport B z.val ∧
          (∀ D : SupportedLocallyFiniteDivisors B W,
            D.val = (fun t ↦ @ite ℤ (t = z.val) (Classical.propDecidable _) 1 0) →
              (e D).val = (fun t ↦ @ite ℤ (t = (r z).val) (Classical.propDecidable _) 1 0)) ∧
          ∃ Z : ClosedSubspace B,
            IsReduced (Z.val : AlgebraicSpace S) ∧
            pointImage Z.val.arrow.hom.hom = spacePrimeSupport B z.val ∧
            IsReduced (enlargedFibreProduct p Z.val.arrow) ∧
            IrreducibleSpace (Point (enlargedFibreProduct p Z.val.arrow).obj.obj) ∧
            pointImage (enlargedFibreProductFst p Z.val.arrow).hom.hom =
              spacePrimeSupport X (r z).val

/-- The affine-local finiteness and absolute separatedness conclusions for p.
All scheme opens are represented over the same ambient base Spec Z.
Source: Stacks, Tags 03KL, 03KQ and 036D
(blueprint: lem-sfb-smooth-integral-fibre-vertical-divisors). -/
def VerticalDivisorAffineFiniteness
    {X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))}
    {T : Over (Spec (.of (ULift.{u} ℤ)))} (p : X ⟶ schemeSpace T) : Prop :=
  ∀ (U : T.left.Opens), IsAffineOpen U →
    CompactSpace (Point (enlargedFibreProduct p
      (groupSchemeMap (Over.homMk (U := Over.mk (U.ι ≫ T.hom)) (V := T) U.ι rfl))).obj.obj) ∧
    IsSeparatedPresheafMap (terminal.from (enlargedFibreProduct p
      (groupSchemeMap (Over.homMk (U := Over.mk (U.ι ≫ T.hom)) (V := T) U.ι rfl))).obj.obj)

/-- The complete vertical-divisor theorem, including locality on the scheme base and
compatibility with every étale base change. In the last clause the vertical arrows
are characterized by Cartier equations, and their existence and uniqueness are explicit.
Thus the compatibility also covers étale splitting of prime divisors.

Source: Stacks, Tags 00ON, 036D, 03ZE, 03KL, 042S, 0AGA and 0EPQ;
Deligne, Le lemme de Gabber, Section 4.2, printed p.142
(blueprint: lem-sfb-smooth-integral-fibre-vertical-divisors).

Proof:
1. Work over an affine open B of T. Smoothness on affine étale charts and regular
smooth ascent make all charts regular and locally Noetherian. Finite presentation
makes X_B quasi-compact. Its separated morphism to affine B, followed by B to Spec Z,
is separated. This proves the affine finiteness assertion.
2. Nonempty geometric fibres imply surjectivity. Faithfully flat field extensions
show ordinary fibres are irreducible; smooth reduced ascent makes them reduced.
Flat locally finitely presented maps are open. Every nonempty open therefore has
nonempty open image meeting V, proving density of X_V, also after open restriction.
3. For an integral closed Z in B, X_B times_B Z is reduced by smooth ascent. Its
surjective open map to the irreducible Z has irreducible fibres, so any two nonempty
opens intersect: intersect their images in Z and then intersect in that fibre.
Separatedness supplies decency by the field-monomorphism lemma. Thus it is integral,
and its unique generic point lies over the generic point of Z.
4. Let xi be the generic point of a vertical prime W and s its image. On an affine
étale chart the flat height formula 00ON reads 1=dim(O_B,s)+dim(O_fibre,xi).
The dense open contains every generic point of B, so the first summand is positive.
It is therefore one, and the fibre dimension is zero. Étale specialization lifting
makes xi the unique generic point of its irreducible fibre.
5. Put Z=closure(s) with reduced structure. Step 3 makes p-inverse(Z) integral with
generic point xi, so reduced-closed-support uniqueness identifies it with W.
Conversely the same height formula shows p-inverse(Z) is a prime divisor for every
base prime Z. Surjectivity gives uniqueness of Z. This yields the prime bijection.
6. The regular prime-divisor local-equation lemma gives a local prime equation t of
Z, a uniformizer at its generic point. Cartier pullback has equation p-star(t).
Its zero space is the reduced inverse image from step 3. At its generic point the
chart local ring A is a DVR and A/tA is reduced and zero-dimensional local, hence a
field. Therefore t generates the maximal ideal of A and has normalized order one.
Other points of the inverse image have codimension at least two by specialization
lifting. The remaining codimension-one orders vanish because t is a unit there.
7. Apply the Cartier/Weil dictionary on each affine base open and its inverse image.
The prime bijection and step 6 give the coefficientwise additive identification.
Quasi-compactness makes every locally finite family finite on each X_B. Uniqueness
of primes gives local finiteness of the descended family on B. Conversely a locally
finite base family pulls back to a locally finite family. These identifications
agree on overlaps and glue, as do Cartier equations in the quotient sheaf.
8. Étale base change preserves regularity, local Noetherianity, openness, density,
smoothness, separatedness and finite presentation. Its geometric fibres are the
same geometric fibres of p. Apply steps 1--7 again. Both composites pull a Cartier
equation t back by the same composite ring homomorphism. Regular units remain units,
so the Cartier quotient and the normalized Weil orders give the commutative square.
No quasi-compactness or separatedness of the étale change of base is needed.

Dependency plan: lem-sfb-stack-chartwise-smooth-etale-calculus,
lem-weil-pbc-smooth-ring-map-iff-smooth-affine, lem-weil-pbc-regular-ring-smooth-ascent,
lem-sfb-space-quasicompact-affine-tests, lem-sfb-space-separated-fp-composition,
lem-weil-pbc-affine-source-morphism-separated, lem-a1-space-point-open-calculus,
lem-weil-pbc-field-extension-base-change-faithfully-flat,
lem-weil-pbc-faithfully-flat-surjective-spectrum, lem-sfb-space-smooth-reduced-locality,
lem-sfb-flat-lfp-space-universally-open, lem-sfb-quasiseparated-space-sober,
lem-sfb-space-reduced-closed-support, lem-sfb-qs-space-field-monomorphism,
lem-weil-pbc-flat-height-formula, lem-sfb-space-local-dimension-chart-invariance,
lem-sfb-quasiseparated-space-etale-specializations,
lem-weil-pbc-reduced-induced-closed-subscheme, lem-sfb-regular-space-divisor-line-dictionary,
lem-per-regular-prime-divisor-local-equations,
lem-weil-pbc-etale-smooth-zero-dimensional-fibres. -/
theorem smoothIntegralFibreVerticalDivisors
    {X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))}
    (T : Over (Spec (.of (ULift.{u} ℤ)))) (p : X ⟶ schemeSpace T)
    (hT : IsRegularScheme T.left) (hp : SmoothIntegralSpaceMap p)
    (V : T.left.Opens) (hV : Dense (V : Set T.left)) :
    VerticalDivisorAffineFiniteness p ∧
      ∃ e : SupportedLocallyFiniteDivisors (schemeSpace T) (schemeOpenPointSet T V) ≃+
          SupportedLocallyFiniteDivisors X
            (mapPoint p.hom.hom ⁻¹' schemeOpenPointSet T V),
        VerticalDivisorIdentification p (schemeOpenPointSet T V) e ∧
        (∀ U : T.left.Opens,
          SmoothIntegralSpaceMap
            (integralSpaceBaseChangeMap p
              (Over.homMk (U := Over.mk (U.ι ≫ T.hom)) (V := T) U.ι rfl)) ∧
          ∃ eU : SupportedLocallyFiniteDivisors
                (schemeSpace (Over.mk (U.ι ≫ T.hom)))
                (schemeOpenPointSet (Over.mk (U.ι ≫ T.hom)) (U.ι ⁻¹ᵁ V)) ≃+
              SupportedLocallyFiniteDivisors
                (enlargedFibreProduct p (groupSchemeMap
                  (Over.homMk (U := Over.mk (U.ι ≫ T.hom)) (V := T) U.ι rfl)))
                (mapPoint (integralSpaceBaseChangeMap p
                  (Over.homMk (U := Over.mk (U.ι ≫ T.hom)) (V := T) U.ι rfl)).hom.hom ⁻¹'
                    schemeOpenPointSet (Over.mk (U.ι ≫ T.hom)) (U.ι ⁻¹ᵁ V)),
            VerticalDivisorIdentification
              (integralSpaceBaseChangeMap p
                (Over.homMk (U := Over.mk (U.ι ≫ T.hom)) (V := T) U.ι rfl))
              (schemeOpenPointSet (Over.mk (U.ι ≫ T.hom)) (U.ι ⁻¹ᵁ V)) eU ∧
            ∃ (ha : MapIsFlat (groupSchemeMap
                (Over.homMk (U := Over.mk (U.ι ≫ T.hom)) (V := T) U.ι rfl)))
              (hb : MapIsFlat (enlargedFibreProductFst p (groupSchemeMap
                (Over.homMk (U := Over.mk (U.ι ≫ T.hom)) (V := T) U.ι rfl)))),
              ∀ D D', IsLocallyFiniteDivisorPullback _ ha D.val D'.val →
                IsLocallyFiniteDivisorPullback _ hb (e D).val (eU D').val) ∧
        ∀ (T' : Over (Spec (.of (ULift.{u} ℤ)))) (a : T' ⟶ T), Etale a.left →
          IsRegularScheme T'.left ∧ Dense (a.left ⁻¹' (V : Set T.left)) ∧
          SmoothIntegralSpaceMap (integralSpaceBaseChangeMap p a) ∧
          VerticalDivisorAffineFiniteness (integralSpaceBaseChangeMap p a) ∧
          ∃ e' : SupportedLocallyFiniteDivisors (schemeSpace T')
                (schemeOpenPointSet T' (a.left ⁻¹ᵁ V)) ≃+
              SupportedLocallyFiniteDivisors (enlargedFibreProduct p (groupSchemeMap a))
                (mapPoint (integralSpaceBaseChangeMap p a).hom.hom ⁻¹'
                  schemeOpenPointSet T' (a.left ⁻¹ᵁ V)),
            VerticalDivisorIdentification (integralSpaceBaseChangeMap p a)
                (schemeOpenPointSet T' (a.left ⁻¹ᵁ V)) e' ∧
            ∃ (ha : MapIsFlat (groupSchemeMap a))
              (hb : MapIsFlat (enlargedFibreProductFst p (groupSchemeMap a))),
              (∀ D : SupportedLocallyFiniteDivisors (schemeSpace T) (schemeOpenPointSet T V),
                ∃! D' : SupportedLocallyFiniteDivisors (schemeSpace T')
                    (schemeOpenPointSet T' (a.left ⁻¹ᵁ V)),
                  IsLocallyFiniteDivisorPullback _ ha D.val D'.val) ∧
              ∀ D D', IsLocallyFiniteDivisorPullback _ ha D.val D'.val →
                IsLocallyFiniteDivisorPullback _ hb (e D).val (e' D').val := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
