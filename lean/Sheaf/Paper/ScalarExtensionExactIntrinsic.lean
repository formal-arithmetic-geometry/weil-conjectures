/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic

import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.IntegralScalarExtensionWellDefined
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated

import Mathlib.CategoryTheory.Triangulated.Triangulated
/-! # Exactness of intrinsic finite scalar extension

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
`sk-prop-sf-pf-reduction/lem-weil-scalar-extension-exact-triangulated.md`
(blueprint: lem-weil-scalar-extension-exact-triangulated).
-/

@[expose] public section
set_option autoImplicit false

universe d u

open CategoryTheory

namespace WeilConjectures

/-- The completed rational scalar extension preserves shifts and distinguished triangles.
Source: blueprint order 1883; Stacks Tags 06XN, 05SE and 05R6
(blueprint: lem-weil-scalar-extension-exact-triangulated).

Proof, following every step of the DAG:

1. Use the completed coefficient sheaves, not discrete constant integral coefficients. Write
$B_m=(A_{L,m})_Y$, with the ring maps $\rho_m$ and restrictions $\operatorname{Res}^L_m$ of
[def-weil-integral-scalar-extension]. For any complex $P$ of $\widehat{\mathcal O}_{E,Y}$-modules,
set $V(P)=\prod_m\operatorname{Res}^L_m(P\otimes_{\widehat{\mathcal O}_{E,Y}}B_m)$ and
$h_P=1-s_P$, and define $H(P)=\operatorname{Cone}(h_P)[-1]$. These termwise products exist by
[lem-weil-proetale-countable-products-exact]. Thus $H(P)^n=V(P)^{n-1}\oplus V(P)^n$, with
differential $(y,x)\mapsto(-dy-h_Px,dx)$. On chain maps use the two diagonal product maps.
Additivity, identities and composition follow componentwise from tensor and product functoriality.
If $k$ is a chain homotopy between $u,v$, its product after tensoring is a degree $-1$ map $\bar
k$ commuting with the transition maps; the degree $-1$ map $k_H(y,x)=(-\bar k y,\bar k x)$ is a
homotopy between $H(u),H(v)$, since the off-diagonal terms cancel and the diagonal terms are
$V(u-v)$. Hence $H$ descends to homotopy categories.

2. The shift comparison $H(P[1])\longrightarrow H(P)[1]$ is $(y,x)\mapsto(-y,x)$ and is natural.
For a chain map $f:P\to Q$, termwise tensoring and products commute with the finite direct sums
defining its cone. Put the four coordinates of $H(C(f))^n$ in the order $(y_Q,y_P,x_Q,x_P)$. The
map $(y_Q,y_P,x_Q,x_P)\mapsto(y_Q,x_Q,-y_P,x_P)$ identifies it with $C(H(f))^n$. Indeed its
differential before this permutation is $(-d_Qy_Q-fy_P-h_Qx_Q,\ d_Py_P-h_Px_P,\ d_Qx_Q+fx_P,\
-d_Px_P)$, which after the permutation is exactly the cone differential of $H(f)$. Its inverse
sends $(a,b,c,d)$ to $(a,-c,b,d)$. This identification respects the cone inclusion. It also
respects the connecting arrow $-p$ using the displayed shift comparison: both maps on the $P$
coordinates are $(y_P,-x_P)$. Therefore $H$ carries cone triangles to cone triangles, including
the last arrow. By [lem-pur-homotopy-category-triangulated], every distinguished homotopy triangle
is isomorphic to such a cone triangle, and the target localization is exact. Consequently
$F=Q_LH:K(\widehat{\mathcal O}_{E,Y})\to D(\widehat{\mathcal O}_{L,Y})$ is exact.

3. Take as resolution class the K-flat complexes with flat terms over $\widehat{\mathcal
O}_{E,Y}$. Every complex admits a quasi-isomorphism from this class by [lem-pc-kflat-resolution].
For a quasi-isomorphism between two members, clause (1) of
[lem-weil-integral-scalar-extension-well-defined] says precisely that its $H$-image is a
quasi-isomorphism, hence $F$ inverts it. Apply [lem-pur-left-derived-from-kflat-class] to the
exact $F$ of step 2 and this class. Its everywhere defined left derived functor is exact and is
computed by $Q_LH(P)$ on every chosen K-flat resolution. This is the functor $K\mapsto
K\otimes_{\mathcal O_E}\mathcal O_L$ specified in [def-weil-integral-scalar-extension], with the
same induced maps and shift comparison; the comparison on resolutions is the natural
derived-functor comparison, not a choice of cones in the triangulated category.

4. The fixed prime satisfies $\ell\neq p$ by [def-weil-rationalization-karoubi], so the
coefficient hypotheses of both following lemmas hold. By
[lem-weil-integral-scalar-extension-constructible] this exact ambient functor maps
$D^b_c(Y,\mathcal O_E)$ into $D^b_c(Y,\mathcal O_L)$. Both are full triangulated subcategories
with the ambient distinguished triangles by [lem-weil-integral-constructible-triangulated],
applied for each coefficient field. Thus on these subcategories its shift comparison remains a
morphism, and the image of every distinguished triangle is still distinguished. Its $\mathcal
O_E$-linearity is clause (3) of [lem-weil-integral-scalar-extension-well-defined]. Denote this
restricted exact linear functor by $T$.

5. By [def-weil-rationalization-karoubi], the specified rational scalar-extension functor is
$T_{L/E}(K)=T(K)$ and $T_{L/E}(f\otimes a)=T(f)\otimes a$, where $a\in E\subset L$. Localize the
shift comparison of $T$ and its inverse. Naturality on $f\otimes a$ is the integral naturality
equation tensored with $a$, and extends to sums by additivity. The two inverse equations also
remain true after tensoring. This supplies a natural isomorphism $T_{L/E}(K[1])\simeq
T_{L/E}(K)[1]$; its iterates give all shifts. No identification of the $\mathcal O_E$- and
$\mathcal O_L$-localizations is needed.

6. Let $\Delta$ be distinguished in $D^b_c(Y,E)$. By
[lem-weil-linear-scalar-localization-triangulated] and [def-weil-rationalization-karoubi], it is
isomorphic to $Q_E(\Delta_0)$ for an integral distinguished triangle $\Delta_0$. With the shift
comparison of step 5, $T_{L/E}(Q_E(\Delta_0))=Q_L(T(\Delta_0))$: all three maps, including the
connecting map, are the integral images tensored with $1$. Step 4 makes $T(\Delta_0)$
distinguished and the cited localization theorem makes its $Q_L$-image distinguished. Applying
$T_{L/E}$ to the triangle isomorphism gives another triangle isomorphism. Hence $T_{L/E}(\Delta)$
is distinguished. Together with step 5 this proves both clauses of the item.
-/
theorem sfScalarExtension_exact_triangulated
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u}) :
    ∃ h : (sfRationalScalarExtension l E Y D.p hl L ι).CommShift ℤ,
      (fun [commShift : (sfRationalScalarExtension l E Y D.p hl L ι).CommShift ℤ] ↦
        (sfRationalScalarExtension l E Y D.p hl L ι).IsTriangulated) (commShift := h) := by
  sorry

end WeilConjectures
