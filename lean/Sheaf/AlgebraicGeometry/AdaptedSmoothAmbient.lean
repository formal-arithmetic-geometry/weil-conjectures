/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Extension.Presentation.Submersive
import Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates
import Mathlib.RingTheory.Kaehler.TensorProduct
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.FiniteType

/-!
# Smooth ambient coordinates adapted to restricted differentials

Source: Bosch--Luetkebohmert--Raynaud, Neron Models, 3.3 Proposition 5,
first two proof paragraphs, printed pp. 68--69
(blueprint: lem-sfb-adapted-smooth-ambient).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace AlgebraicGeometry

/-- Locally along a smooth special-fibre centre with finite locally free restricted
cotangent sheaf, a scheme has smooth affine ambient coordinates inducing an isomorphism
on that restricted cotangent sheaf.

Here `i` is the composite closed immersion into `X`, and `hq` specifies its factorization
through the special fibre. The inverse-image open `i ⁻¹ᵁ V` is the scheme `W`.
The surjections `f` and `g`, together with `eD` and `eE`, identify `D` and `E` with the
coordinate rings of `V` and `W`. Thus `E` is canonically `C / ker (f ≫ g)`.
The final formula fixes the differential isomorphism on all pure differential tensors;
it is precisely the canonical map, with the tensor factors written in reverse order.

Source: BLR, Neron Models, 3.3 Proposition 5 proof, printed pp. 68--69
(blueprint: lem-sfb-adapted-smooth-ambient).

Proof:
1. Fix $u\in U$. Since $Y$ is closed in $X$ and $Y\setminus U$ is closed in $Y$, choose an
affine finite-type neighbourhood $V_0=\operatorname{Spec}D$ of $u$ disjoint from $Y\setminus U$.
Shrink it further so that, with $W_0=Y\cap V_0=\operatorname{Spec}E$, $\Omega_{D/R}\otimes_DE$
is free of constant rank $q$. This is exactly the assumed local freeness, interpreted by
[def-sc-relative-differential-sheaf]. Write $E=D/I$; $\pi\in I$ because $W_0$ lies in the
special fibre. Choose finitely many algebra generators of $D$ and the resulting surjection
$P=R[T_1,\ldots,T_N]\twoheadrightarrow D$, with kernel $K$. Its spectrum is the initial closed
embedding. Subsequent shrinking of an affine scheme will always be to a principal open
containing $u$; the inverse image in $V_0$ is then a principal affine open as well.
Dependencies: def-weil-finite-type-morphism, def-sc-relative-differential-sheaf,
def-weil-closed-immersion.
2. Apply [lem-weil-pbc-jacobi-zariski-differential-maps] to $P\twoheadrightarrow D$ and tensor
the resulting right exact sequence with $\kappa(u)$ using [lem-weil-pbc-tensor-right-exact]. By
[lem-weil-pbc-polynomial-ring-kahler-basis], its middle term is $\kappa(u)^N$ and its last term
has dimension $q$. Therefore the vectors $dh$ for $h\in K$ span a kernel of dimension $c=N-q$.
Select $h_1,\ldots,h_c\in K$ whose differential vectors are a basis of this kernel. Select $c$
rows giving a nonzero square minor, and reorder the variables so they are the first $c$. Let
$\Delta=\det(\partial h_j/\partial T_i)_{1\leq i,j\leq c}$. Then $\Delta(u)\ne0$. For $c=0$ use
the empty list and $\Delta=1$. Dependencies: lem-weil-pbc-jacobi-zariski-differential-maps,
lem-weil-pbc-tensor-right-exact, lem-weil-pbc-polynomial-ring-kahler-basis.
3. Set $B=P/(h_1,\ldots,h_c)$ and $C_0=B[1/\Delta]$. Replace $D$ by $D[1/\Delta]$ and $E$ by its
corresponding localization. Since every $h_j$ belongs to $K$, there is still a surjection
$C_0\twoheadrightarrow D$. The presentation $C_0=R[T_1,\ldots,T_N,t]/(h_1,\ldots,h_c,t\Delta-1)$
is standard smooth: use the pivot variables $T_1,\ldots,T_c,t$. Its determinant is $\Delta^2$,
since the upper-right block is zero and the last diagonal entry is $\Delta$. Thus
[lem-weil-pbc-standard-smooth-is-smooth] and [lem-weil-pbc-smooth-ring-map-iff-smooth-affine]
show that $\operatorname{Spec}C_0$ is smooth over $R$. By
[lem-weil-pbc-standard-smooth-kahler-basis], $\Omega_{C_0/R}$ is free on the remaining $q=N-c$
variable differentials. Dependencies: def-weil-pbc-standard-smooth-algebra,
lem-weil-pbc-standard-smooth-is-smooth, lem-weil-pbc-smooth-ring-map-iff-smooth-affine,
lem-weil-pbc-standard-smooth-kahler-basis.
4. The canonical map $\Omega_{C_0/R}\otimes_{C_0}E\to\Omega_{D/R}\otimes_DE$ is surjective by
[lem-weil-pbc-jacobi-zariski-differential-maps] and [lem-weil-pbc-tensor-right-exact]. Both
modules are free of rank $q$. Choose bases. At $u$ its matrix is a surjective square matrix over
$\kappa(u)$, so its determinant is nonzero. Invert a lift of that determinant from $E$ to $C_0$.
The adjugate formula gives an inverse on all of the resulting $W_0$. Rename the localized rings
$C_0,D,E$. Their differential modules have the claimed localizations by
[lem-weil-pbc-kahler-differentials-localization]. In particular the canonical restricted
differential map is now an isomorphism, not merely an isomorphism on one residue fibre.
Dependencies: lem-weil-pbc-jacobi-zariski-differential-maps, lem-weil-pbc-tensor-right-exact,
lem-weil-pbc-kahler-differentials-localization.
5. Every principal localization of our standard smooth presentation is again standard smooth: to
invert an element represented by $g$, append a variable $s$ and the equation $sg-1$, and append
$s$ to the pivot variables. The new determinant is the old determinant times $g$, a unit. Thus
all the preceding principal shrinkings preserve standard smoothness. By
[lem-weil-pbc-standard-smooth-base-change] the special fibre
$Z_{0,k}=\operatorname{Spec}(C_0/\pi C_0)$ is standard smooth over $k$, and
[lem-weil-pbc-standard-smooth-is-smooth] and [lem-weil-pbc-smooth-ring-map-iff-smooth-affine]
make it smooth over $k$. The closed subscheme $W_0$ is smooth over $k$ by the hypothesis
$W_0\subset U$. Dependencies: def-weil-pbc-standard-smooth-algebra,
lem-weil-pbc-standard-smooth-base-change, lem-weil-pbc-standard-smooth-is-smooth,
lem-weil-pbc-smooth-ring-map-iff-smooth-affine.
6. Apply [lem-pur-smooth-pair-local-coordinates] to $W_0\hookrightarrow Z_{0,k}$ over
$\operatorname{Spec}k$. It gives, near $u$, an etale chart with coordinate functions $\bar
y_1,\ldots,\bar y_r,\bar z_1,\ldots,\bar z_n$, whose last coordinates cut out $W_0$
scheme-theoretically. Choose a principal affine neighbourhood of $u$ contained in the chart, and
lift its defining denominator to $C_0$. Localize $C_0,D,E$ accordingly. The chart functions now
belong to $C_0/\pi C_0$. Lift them to functions $y_i,z_j\in C_0$. If $J_0=\ker(C_0\to E)$, the
coordinate-subspace assertion gives $J_0/\pi C_0=(\bar z_1,\ldots,\bar z_n)$, so
$J_0=(\pi,z_1,\ldots,z_n)$. The chosen $z_j$ belong to $J_0$ since their images in $E$ are zero.
Dependencies: lem-pur-smooth-pair-local-coordinates.
7. By [lem-sfb-etale-localization-relative-differentials], applied to this etale chart and the
identity of $\operatorname{Spec}k$, and [lem-weil-pbc-polynomial-ring-kahler-basis], the
differentials $d\bar y_i,d\bar z_j$ are a basis of $\Omega_{(C_0/\pi C_0)/k}$. By
[lem-weil-pbc-kahler-differentials-base-change], this module is
$\Omega_{C_0/R}\otimes_{C_0}(C_0/\pi C_0)$ with exactly these lifted differential vectors. Since
$\Omega_{C_0/R}$ is free of rank $q$, reducing at $u$ shows $r+n=q$. The matrix of $dy_i,dz_j$
in its existing basis has determinant nonzero at $u$. Invert this determinant. Its adjugate
supplies an inverse matrix, so $dy_i,dz_j$ form a basis of $\Omega_{C_0/R}$ on the resulting
affine neighbourhood. Dependencies: lem-sfb-etale-localization-relative-differentials,
lem-weil-pbc-polynomial-ring-kahler-basis, lem-weil-pbc-kahler-differentials-base-change.
8. Consider $g=(y_i,z_j):\operatorname{Spec}C_0\to\mathbf A^{r+n}_R$. Its source is smooth by
the standard smooth construction and its target is smooth by [sbc-lem-affine-space-smooth]. By
[lem-weil-pbc-polynomial-ring-kahler-basis], the relative differential map for $g$ sends the
coordinate basis to the basis $dy_i,dz_j$. Therefore
[lem-sfb-smooth-morphism-cotangent-isomorphism-etale] supplies an open neighbourhood of $u$ on
which $g$ is etale. Choose a principal affine neighbourhood inside it and denote its ring by
$C$. Its inverse image in $\operatorname{Spec}D$ is the final $V$, with ring again denoted $D$.
Restriction preserves the coordinate differential basis and the isomorphism along $W$ by
[lem-weil-pbc-kahler-differentials-localization]. Dependencies: sbc-lem-affine-space-smooth,
lem-weil-pbc-polynomial-ring-kahler-basis, lem-sfb-smooth-morphism-cotangent-isomorphism-etale,
lem-weil-pbc-kahler-differentials-localization.
9. Let $E=\mathcal O_W(W)$ for the final $W=Y\cap V$. The final surjections $C\twoheadrightarrow
D\twoheadrightarrow E$ give $H=\ker(C\to D)\subseteq J=\ker(C\to E)$. The equality
$J=(\pi,z_1,\ldots,z_n)$ persists under each localization: an element maps to zero after
localization precisely when a power of the inverted element times a numerator maps to zero
before localization. The isomorphism of restricted differential modules established in step 4
and preserved in steps 6--8 is the canonical map in the statement, because on every generator it
is $dc\otimes e\mapsto d(c|_D)\otimes e$. All localizations were made at elements nonzero at
$u$, so $u\in V$ and $W\subset U$. Dependencies: .
10. The ring $R$ is Noetherian: by [def-sc-discrete-valuation-ring] every ideal is principal.
The ring $C$ is finite type over $R$, since it was obtained from a quotient of a polynomial ring
in finitely many variables by finitely many principal localizations (each inverse is one
additional algebra generator). Hence [lem-weil-pbc-finite-type-algebra-noetherian] makes $C$
Noetherian. The construction worked at the arbitrary chosen $u$ and used no flatness of $X$,
smoothness of its generic fibre, density condition, or group law. Dependencies:
def-sc-discrete-valuation-ring, lem-weil-pbc-finite-type-algebra-noetherian. -/
theorem Scheme.Hom.exists_adapted_smooth_ambient
    (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) {X Y : Scheme.{u}}
    (p : X ⟶ Spec R) [LocallyOfFiniteType p]
    (i : Y ⟶ X) [IsClosedImmersion i]
    (q : Y ⟶ Spec (.of (IsLocalRing.ResidueField R)))
    (hq : i ≫ p = q ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (U : Y.Opens) [Smooth (U.ι ≫ q)]
    (hfree : ((Scheme.Modules.tensorPullback (U.ι ≫ i)).obj
      p.relativeDifferentials).IsFiniteLocallyFree) (u₀ : U.toScheme) :
    ∃ (V : X.Opens) (C D E : CommRingCat.{u}) (a : R ⟶ C)
      (f : C ⟶ D) (g : D ⟶ E) (eD : V.toScheme ≅ Spec D)
      (eE : (i ⁻¹ᵁ V).toScheme ≅ Spec E) (r n : ℕ)
      (y : Fin r → C) (z : Fin n → C)
      (b : Module.Basis (Fin (r + n)) C (CommRingCat.KaehlerDifferential a))
      (α : (ModuleCat.extendScalars (f ≫ g).hom).obj
          (CommRingCat.KaehlerDifferential a) ≅
        (ModuleCat.extendScalars g.hom).obj (CommRingCat.KaehlerDifferential (a ≫ f))),
      i (U.ι u₀) ∈ V ∧ (i ⁻¹ᵁ V) ≤ U ∧
      eD.hom ≫ Spec.map (a ≫ f) = V.ι ≫ p ∧
      eE.hom ≫ Spec.map g = (i ∣_ V) ≫ eD.hom ∧
      Function.Surjective f ∧ Function.Surjective g ∧
      Smooth (Spec.map a) ∧ LocallyOfFiniteType (Spec.map a) ∧
      QuasiCompact (Spec.map a) ∧
      RingHom.ker f.hom ≤ RingHom.ker (f ≫ g).hom ∧
      RingHom.ker (f ≫ g).hom = Ideal.span ({a π} ∪ Set.range z) ∧
      Etale (Spec.map (CommRingCat.ofHom
        (MvPolynomial.eval₂Hom a.hom
          (fun j : ULift.{u} (Fin (r + n)) ↦ Fin.addCases y z j.down))) ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin (r + n))) R).inv) ∧
      (∀ j : Fin (r + n), b j =
        CommRingCat.KaehlerDifferential.d (f := a) (Fin.addCases y z j)) ∧
      IsNoetherianRing C ∧
      ∀ (c : C) (e : E),
        α.hom (e ⊗ₜ[C, (f ≫ g).hom] CommRingCat.KaehlerDifferential.d (f := a) c) =
          e ⊗ₜ[D, g.hom] CommRingCat.KaehlerDifferential.d (f := a ≫ f) (f c) := by
  sorry

end AlgebraicGeometry
