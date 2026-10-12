/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteSplitEtaleHypercover

/-! Intermediate construction for finite split hypercover refinement. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- Source: Stacks Project, Hypercoverings, Tags 0DAV, 094K, 01GS.

Proof: Finite limits of qcqs etale schemes over the qcqs base are qcqs etale: fibre
products have this property, and equalizers are pullbacks of the quasi-compact diagonals.
Thus the finite matching diagram of a finite qcqs skeleton has a qcqs etale limit, also
universal among all schemes over X. Cover this limit by finitely many affine opens. An
etale cover of each such open has a finite affine refinement, since its affine members
have open images covering a quasi-compact space. The chosen affine pieces are qcqs and
of finite presentation over X; their structure maps are quasi-compact and quasi-separated.
Construct a split hypercover by induction on $n$. In degree zero take such a finite affine
etale covering of $X$. Given the split skeleton below $n$, form its matching object
$M_n(U)$. The degeneracies already prescribe one copy of each earlier nondegenerate summand for
every surjection $(n)\twoheadrightarrow(m)$, $m<n$, and give maps from those copies to $M_n(U)$.
On every matching component, including components met by degenerate copies, choose a finite
affine etale covering as above and call the disjoint union of these new pieces $N_n$. Then
$U_n$ is the coproduct of the degenerate copies with $N_n$; its map to $M_n(U)$ is a cover
because $N_n$ covers every component. For a nondegenerate $n$-simplex, every proper face is the
corresponding projection of its matching map, and those faces satisfy all face-face identities
because they form a compatible point of $M_n(U)$. For a degenerate copy indexed by a surjection
$\sigma:(n)\twoheadrightarrow(m)$ and an $m$-simplex $i$, compose any simplicial operator into
$(n)$ with $\sigma$, factor that composite uniquely as a surjection followed by an injection,
apply the old face indexed by the injection to $i$, and place the result in the degeneracy copy
indexed by the surjection. This also defines each degeneracy of an old simplex as the
corresponding copy. For two composable simplicial operators, the epi-mono factorization of their
composite is the factorization obtained by repeating this rule, so their actions agree; when the
last simplex is nondegenerate, the only extra case is two proper faces, already checked by the
matching equations. This verifies the simplicial identities that Stacks 0DAV leaves implicit.
Repeating for every $n$ gives a hypercover finite in each degree as defined in (def-weil-pbc-
finite-split-hypercover).
(blueprint: lem-weil-pbc-finite-split-hypercover-existence) -/
theorem exists_finite_split_hypercover (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] : Nonempty (FiniteSplitEtaleHypercover X) := by
  sorry

end AlgebraicGeometry.FiniteSplitEtaleHypercover
