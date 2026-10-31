/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Algebra.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso
import WeilConjectures.RingTheory.StandardSmoothDimensionAtPoints
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import WeilConjectures.AlgebraicGeometry.NormalSectionsFiniteProduct
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Extension.Presentation.Submersive
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.FiniteType

/-! # The relative Fermat curve as a two-root Kummer cover

Source: de Jong, Families of curves and alterations, §3.5, p.607 (the cover C_i);
Stacks Project, Tags 0BYA and 0BYD, Plane curves and the genus of a plane curve.
(blueprint: lem-sfb-fermat-kummer-relative-curve)

The equation is a genuine zero scheme of a section of the tensor power of O(1).
The two chart identities specify the morphism, including its value over infinity.
The generic-field algebra is constrained by its map to the projective line; the
normalization is taken with respect to this algebra, rather than an arbitrary embedding.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.RelativeFermatCurve

/-- The homogeneous equation A^l - B^l - C^l as a section of O(1) tensor-powered l times.
Source: Stacks 0BYA, the Fermat example, with the displayed signs of the Kummer cover.
(blueprint: lem-sfb-fermat-kummer-relative-curve) -/
noncomputable def equation (U : Scheme.{u}) (l : ℕ) :
    𝟙_ (ProjectiveSpace (ULift.{u} (Fin 3)) U).Modules ⟶
      (ProjectiveSpace.twist (ULift.{u} (Fin 3)) U 1).tensorPow l :=
  Scheme.Modules.tensorPowSection
      (ProjectiveSpace.coordinateSection (ULift.{u} (Fin 3)) U ⟨0⟩) l -
    Scheme.Modules.tensorPowSection
      (ProjectiveSpace.coordinateSection (ULift.{u} (Fin 3)) U ⟨1⟩) l -
    Scheme.Modules.tensorPowSection
      (ProjectiveSpace.coordinateSection (ULift.{u} (Fin 3)) U ⟨2⟩) l

/-- The ideal sheaf of the homogeneous Fermat equation, without taking its radical.
Source: Stacks 0BYA, the closed plane curve defined by its homogeneous equation.
(blueprint: lem-sfb-fermat-kummer-relative-curve) -/
noncomputable def ideal (U : Scheme.{u}) (l : ℕ) :
    (ProjectiveSpace (ULift.{u} (Fin 3)) U).IdealSheafData :=
  Scheme.Modules.Hom.zeroLocus (equation U l)

/-- The relative Fermat closed subscheme A^l - B^l = C^l of the projective plane over U.
Source: Stacks 0BYA; de Jong §3.5, p.607, the two-root cover.
(blueprint: lem-sfb-fermat-kummer-relative-curve) -/
noncomputable def curve (U : Scheme.{u}) (l : ℕ) : Scheme.{u} :=
  (ideal U l).subscheme

/-- The specified closed embedding of the relative Fermat curve in the plane.
Source: Stacks 0BYA, the given plane embedding.
(blueprint: lem-sfb-fermat-kummer-relative-curve) -/
noncomputable def ι (U : Scheme.{u}) (l : ℕ) :
    curve U l ⟶ ProjectiveSpace (ULift.{u} (Fin 3)) U :=
  (ideal U l).subschemeι

/-- The structure morphism of the relative Fermat curve over its base.
Source: de Jong §3.5, p.607, the relative cover C_i over U_i.
(blueprint: lem-sfb-fermat-kummer-relative-curve) -/
noncomputable def π (U : Scheme.{u}) (l : ℕ) : curve U l ⟶ U :=
  ι U l ≫ ProjectiveSpace (ULift.{u} (Fin 3)) U ↘ U

/-- The relative Fermat curve is the smooth high-genus normalization in the two-root field.
Source: de Jong §3.5, p.607; Stacks Tags 0BYA and 0BYD.
(blueprint: lem-sfb-fermat-kummer-relative-curve)

Proof, following the nine DAG steps:
1. Over an affine base open $V=\operatorname{Spec}R$, use the standard Proj opens: a homogeneous
degree-zero fraction with denominator a power of $C$ is a polynomial in $A/C,B/C$. The same
calculation applies with denominator $A$. The affine base-change identification transports these
charts from $\mathbf Z$ to $R$, by tensoring their polynomial presentations. Thus $D_+(C)\cap
C_\ell=\operatorname{Spec}R[a,b]/(a^\ell-b^\ell-1)$ and $D_+(A)\cap
C_\ell=\operatorname{Spec}R[u,v]/(u^\ell+v^\ell-1)$, where $(a,b)=(A/C,B/C)$ and
$(u,v)=(B/A,C/A)$. They cover: a homogeneous prime containing $A,C$ also contains $B$ by the
equation, hence is irrelevant. Map the first chart to the $x$-chart by $x=a^\ell$, and the
second to the $y$-chart by $y=v^\ell$. On the overlap $v=a^{-1}$ and $u=b/a$, so $y=x^{-1}$. The
morphism-gluing lemma, also on overlaps of base opens, gives $\rho$ with precisely the stated
formula.
   Uses: def-pc-proj, lem-weil-pbc-affine-chart-base-change-iso, lem-weil-pbc-scheme-morphism-
gluing.
2. The inverse image of the $x$-chart is exactly the $C$-chart, and its algebra has the
presentation $R[x,a,b]/(a^\ell-x,b^\ell-(x-1))$. Apply the monic-quotient power-basis lemma
first to $a^\ell-x$ and then over that quotient to $b^\ell-(x-1)$. It is free over $R[x]$ with
basis $a^i b^j$, $0\leq i,j<\ell$, in particular finite. The other chart similarly has
presentation $R[y,u,v]/(v^\ell-y,u^\ell-(1-y))$ and basis $u^i v^j$. These are affine inverse
images of an affine cover of $\mathbf P^1_U$, so finiteness local on the target proves that
$\rho$ is finite.
   Uses: lem-weil-pbc-monic-quotient-free, lem-weil-pbc-finite-local-on-target.
3. For a point of $\mathbf P^1_U$ with finite coordinate $x=t$ in its residue field, choose an
algebraic closure $\Omega$ of that field. The polynomials $T^\ell-t$ and $T^\ell-(t-1)$ have
roots $a,b$ in $\Omega$, giving the point $[a:b:1]$ of $C_\ell$ mapping to the chosen point.
Above infinity use $[1:1:0]$. This proves surjectivity on all points, including points over
nonclosed points of $U$. Existence of the closure and its root property are exactly the
algebraic-closure node.
   Uses: def-weil-algebraic-closure.
4. Both chart equations have the form $f=s^\ell+\epsilon t^\ell-1$, where $\epsilon=\pm1$. The
opens $D(s),D(t)$ cover, since $(s,t)$ contains $1$ in the quotient. On $D(s)$ write its ring as
$R[s,z,t]/(f,sz-1)$; the Jacobian determinant for the first two variables $(s,z)$ is $\ell
s^\ell$, a unit. On $D(t)$, using variables $(t,z,s)$ and relation $tz-1$, the determinant is
$\epsilon\ell t^\ell$, also a unit. These are standard smooth presentations with $n=3,c=2$.
Standard smooth algebras are smooth ring maps, so each $\operatorname{Spec}$ of these localized
chart rings is smooth over $\operatorname{Spec}R$ by the ring-map/affine-morphism equivalence.
Composing with the open immersion $\operatorname{Spec}R=V\subseteq U$ keeps it smooth (open-
subscheme lemma, part (b)), and these opens, over all $V$, cover $C_\ell$; smoothness is local
on the source, so $C_\ell\to U$ is smooth. For a field $L$ with a map $R\to L$, the base-change
lemma for standard smooth presentations gives the same presentations with coefficients in $L$,
and the standard-smooth dimension theorem gives dimension $3-2=1$ at every point of each fibre.
The given closed embedding into $\mathbf P^2_U$ makes the morphism H-projective by definition.
   Uses: def-weil-pbc-standard-smooth-algebra, lem-weil-pbc-standard-smooth-is-smooth, lem-weil-
pbc-smooth-ring-map-iff-smooth-affine, lem-weil-pbc-smooth-restrict-open-subschemes, lem-weil-pbc-
smooth-local-on-source, def-sbc-smooth-morphisms, lem-weil-pbc-standard-smooth-base-change, lem-
weil-pbc-standard-smooth-over-field-dimension-at-points, def-kun-projective.
5. Let $L$ be any field equipped with a point $\operatorname{Spec}L\to U$. The fibre after this
extension is the plane hypersurface $A^\ell-B^\ell-C^\ell=0$ over $L$: if
$\operatorname{Spec}L\to U$ lands in the base open $V=\operatorname{Spec}R$, the affine base-
change identification gives the charts $\operatorname{Spec}(L\otimes_R
R[a,b]/(a^\ell-b^\ell-1))=\operatorname{Spec}L[a,b]/(a^\ell-b^\ell-1)$ and likewise for the
$A$-chart, with the same gluing as in step 1, and these are the standard Proj charts of
$\operatorname{Proj}(L[A,B,C]/(A^\ell-B^\ell-C^\ell))$. Its equation remains nonzero homogeneous
of degree $\ell$. The plane-hypersurface cohomology lemma gives $\Gamma(C_{\ell,L},\mathcal
O)=L$. It is nonempty because $[1:0:1]$ is an $L$-point. In a field an idempotent satisfies
$e(e-1)=0$, hence is $0$ or $1$; the connectedness/idempotents lemma therefore proves
connectedness. The identical argument over every further field extension proves that every fibre
is geometrically connected.
   Uses: lem-weil-pbc-affine-chart-base-change-iso, def-pc-proj, lem-sfb-plane-hypersurface-
cohomology, lem-pc-scheme-connected-iff-idempotents.
6. Apply the normal-integral smooth-family geometry core to $C_\ell\to U$: the base is integral
with integrally closed local rings by hypothesis, the map is smooth by step 4, its fibres are
geometrically connected by step 5, and its source is nonempty by $[1:0:1]$. It follows that
$C_\ell$ is integral and all its local rings are integrally closed. For each $L$ as in step 5,
apply the same core to $C_{\ell,L}\to\operatorname{Spec}L$. A field is an integrally closed
domain, and smoothness and geometric connectedness for this map were proved directly over $L$
and its extensions. Thus $C_{\ell,L}$ is integral for every such $L$. This is geometric
integrality of every fibre. Step 4 supplies their dimension one.
   Uses: lem-sbc-smooth-connected-generic-geometry-core, def-pc-geometrically-irreducible.
7. For a geometric fibre over an algebraically closed field $\Omega$, steps 4 and 6 give a
smooth projective geometrically integral curve. By the definition of genus its genus is
$\dim_\Omega H^1(C_{\ell,\Omega},\mathcal O)$. Substituting $d=\ell$ into the plane-hypersurface
cohomology lemma gives $(\ell-1)(\ell-2)/2$. Since $\ell\geq5$, the product is at least
$4\cdot3$, and the genus is at least $6$, hence at least $2$.
   Uses: lem-sfb-plane-hypersurface-cohomology, def-pc-genus.
8. Choose a nonempty affine base open $\operatorname{Spec}R\subset U$, and put
$K=k(U)=\operatorname{Frac}R$ using the affine function-field theorem. The corresponding
$C$-chart is nonempty (it contains $[1:0:1]$), hence is an affine open of the integral scheme
$C_\ell$. Its fraction field is $k(C_\ell)$ by the same theorem. Localizing its ring at
$R\setminus\{0\}$ identifies that fraction field with
$\operatorname{Frac}(K[a,b]/(a^\ell-b^\ell-1))$. The free basis from step 2 proves that $K[x]$
injects in this ring under $x=a^\ell$, so $x$ is transcendental over $K$. Its fraction field is
generated over $K(x)$ by $a,b$, and the defining equations are exactly $a^\ell=x$, $b^\ell=x-1$.
The monic equations show that this extension is finite. Thus this is the field in the assertion,
with its specified embedding of $K(x)$.
   Uses: lem-sc-integral-function-field-affine-fraction, lem-weil-pbc-monic-quotient-free.
9. First check that the normalization base $\mathbf P^1_U$ is integral. Its affine chart rings
$R[x]$ and $R[y]$ are domains, since $R$ is a domain and leading coefficients multiply; thus it
is reduced. Two nonempty target opens have nonempty inverse images by step 3, and these
intersect because $C_\ell$ is irreducible by step 6. Thus the target is nonempty and
irreducible, hence integral. Its affine-chart fraction field is $K(x)$ by the affine function-
field theorem. Work on a cover of $U$ by affine opens whose rings are finitely generated over
the ground field, as provided by finite type. Each inverse-image ring $S$ of a target chart in
step 2 is also a finitely generated algebra over that field, so is Noetherian by the affine-
Noetherian lemma. Its spectrum is an open of the normal integral scheme $C_\ell$. The normal-
sections lemma makes $S$ a finite product of integrally closed domains. Since $S$ is a nonzero
domain, a product decomposition has exactly one factor, so $S$ itself is integrally closed. Its
fraction field is the field $L=k(C_\ell)$ by the affine function-field theorem. If $B$ is the
corresponding ring $R[x]$ or $R[y]$, step 2 makes $S$ integral over $B$, and $B\subset S\subset
L$. Conversely, an element $z\in L$ integral over $B$ satisfies the same monic equation over
$S$, so belongs to $S$ by its integral closedness. Thus $S$ is precisely the integral closure of
$B$ in $L$. On overlaps these equalities are compatible with localization and the coordinate
substitutions of step 1. The affine definition of normalization therefore identifies
$\rho:C_\ell\to\mathbf P^1_U$ with the normalization in $L$.
   Uses: def-weil-finite-type-morphism, lem-wf-affine-noetherian-components, lem-sbc-normal-
sections-finite-product, lem-sc-integral-function-field-affine-fraction, def-fin-normalization-
extension, def-pc-integral-scheme.
-/
theorem exists_finite_kummer_cover
    (k : Type u) [Field k] (U : Scheme.{u}) [IsIntegral U]
    (p : U ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hnormal : ∀ z : U, IsDomain (U.presheaf.stalk z) ∧
      IsIntegrallyClosed (U.presheaf.stalk z))
    (l : ℕ) (hl : Nat.Prime l) (hl5 : 5 ≤ l)
    (hinv : IsUnit (l : Γ(U, ⊤)))
    (hroot : ∃ ζ : Γ(U, ⊤), IsPrimitiveRoot ζ l) :
    ∃ (_ : IsIntegral (curve U l))
      (_ : IsIntegral (ProjectiveSpace (ULift.{u} (Fin 2)) U))
      (ρ : curve U l ⟶ ProjectiveSpace (ULift.{u} (Fin 2)) U)
      (hC : ρ ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) U ⟨1⟩ =
        ι U l ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin 3)) U ⟨2⟩)
      (hA : ρ ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) U ⟨0⟩ =
        ι U l ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin 3)) U ⟨0⟩),
      ρ ≫ ProjectiveSpace (ULift.{u} (Fin 2)) U ↘ U = π U l ∧
      IsFinite ρ ∧ Surjective ρ ∧
      (∀ z : curve U l, IsDomain ((curve U l).presheaf.stalk z) ∧
        IsIntegrallyClosed ((curve U l).presheaf.stalk z)) ∧
      Smooth (π U l) ∧ IsHProjective (π U l) ∧ GeometricallyIntegral (π U l) ∧
      SmoothOfRelativeDimension 1 (π U l) ∧
      ρ.appLE (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) U ⟨1⟩)
          (ι U l ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin 3)) U ⟨2⟩) hC.ge
          (ProjectiveSpace.coordRatio (ULift.{u} (Fin 2)) U ⟨1⟩ ⟨0⟩) =
        ((ι U l).app _
          (ProjectiveSpace.coordRatio (ULift.{u} (Fin 3)) U ⟨2⟩ ⟨0⟩)) ^ l ∧
      ρ.appLE (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) U ⟨0⟩)
          (ι U l ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin 3)) U ⟨0⟩) hA.ge
          (ProjectiveSpace.coordRatio (ULift.{u} (Fin 2)) U ⟨0⟩ ⟨1⟩) =
        ((ι U l).app _
          (ProjectiveSpace.coordRatio (ULift.{u} (Fin 3)) U ⟨0⟩ ⟨2⟩)) ^ l ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U),
        @Scheme.arithmeticGenus Ω _ (pullback (π U l) s) ⟨pullback.snd (π U l) s⟩ =
          (l - 1) * (l - 2) / 2 ∧
        2 ≤ @Scheme.arithmeticGenus Ω _ (pullback (π U l) s)
          ⟨pullback.snd (π U l) s⟩) ∧
      ∃ (_ : Nonempty (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) U ⟨1⟩))
        (_ : Nonempty (ι U l ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin 3)) U ⟨2⟩))
        (e : RatFunc U.functionField ≃+*
          (ProjectiveSpace (ULift.{u} (Fin 2)) U).functionField)
        (_ : Algebra (ProjectiveSpace (ULift.{u} (Fin 2)) U).functionField
          (curve U l).functionField),
        e RatFunc.X =
          (ProjectiveSpace (ULift.{u} (Fin 2)) U).germToFunctionField _
            (ProjectiveSpace.coordRatio (ULift.{u} (Fin 2)) U ⟨1⟩ ⟨0⟩) ∧
        Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
            (ProjectiveSpace (ULift.{u} (Fin 2)) U).fromSpecFunctionField ≫
              ProjectiveSpace (ULift.{u} (Fin 2)) U ↘ U =
          Spec.map (CommRingCat.ofHom (algebraMap U.functionField (RatFunc U.functionField))) ≫
            U.fromSpecFunctionField ∧
        Spec.map (CommRingCat.ofHom (algebraMap
            (ProjectiveSpace (ULift.{u} (Fin 2)) U).functionField (curve U l).functionField)) ≫
              (ProjectiveSpace (ULift.{u} (Fin 2)) U).fromSpecFunctionField =
          (curve U l).fromSpecFunctionField ≫ ρ ∧
        FiniteDimensional (ProjectiveSpace (ULift.{u} (Fin 2)) U).functionField
          (curve U l).functionField ∧
        (∃ a b : (curve U l).functionField,
          a = (curve U l).germToFunctionField _ ((ι U l).app _
            (ProjectiveSpace.coordRatio (ULift.{u} (Fin 3)) U ⟨2⟩ ⟨0⟩)) ∧
          b = (curve U l).germToFunctionField _ ((ι U l).app _
            (ProjectiveSpace.coordRatio (ULift.{u} (Fin 3)) U ⟨2⟩ ⟨1⟩)) ∧
          a ^ l = algebraMap _ _ (e RatFunc.X) ∧
          b ^ l = algebraMap _ _ (e RatFunc.X - 1) ∧
          IntermediateField.adjoin
            (ProjectiveSpace (ULift.{u} (Fin 2)) U).functionField {a, b} = ⊤) ∧
        ∃ E : curve U l ≅ (ProjectiveSpace (ULift.{u} (Fin 2)) U).normalizationIn
            (curve U l).functionField,
          E.hom ≫ (ProjectiveSpace (ULift.{u} (Fin 2)) U).fromNormalizationIn
            (curve U l).functionField = ρ := by
  sorry

end AlgebraicGeometry.RelativeFermatCurve
