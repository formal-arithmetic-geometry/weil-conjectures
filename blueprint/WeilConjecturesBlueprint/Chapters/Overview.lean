import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Overview" =>

This blueprint tracks a Lean 4 formalization of the *Weil conjectures* for
smooth, proper, geometrically integral varieties over finite fields:
rationality of the zeta function, the functional equation, and the Riemann
hypothesis. The target statements are already fixed in the repository
(`AlgebraicGeometry.Scheme.weil_conjectures` and
`AlgebraicGeometry.Scheme.zetaSeries_rational`), formulated purely
arithmetically: the zeta function is defined by point counts, and the three
conjectures are stated as properties of integer polynomials
$`P_0, \dots, P_{2d} \in \ZZ[t]` and of the complex roots of their images in
$`\CC[t]`. No cohomology appears in the final statements.

# Architecture: three layers

The formalization is organized in three layers, obtained by backward chaining
from the final theorem.

1. *Version I — the elementary Frobenius-module theorem.* All arithmetic
   content of the Weil conjectures is proved as a linear-algebra theorem over
   an abstract algebraically closed field $`K` of characteristic $`0`: given
   finite-dimensional $`K`-vector spaces $`H^0, \dots, H^{2d}` with
   automorphisms $`F_i` satisfying a trace formula, similitude pairings, an
   endpoint normalization, and universal purity, all conclusions follow. This
   layer has no geometric dependencies and is the current focus.

2. *Version II — the abstract cohomology package.* The hypotheses of
   Version I are packaged as an interface (temporary axioms
   AX1–AX4) attached to each smooth projective variety.

3. *Version III — the étale realization.* ℓ-adic étale cohomology
   satisfies the interface. This layer contains the deep inputs:
   the Grothendieck–Lefschetz trace formula, Poincaré duality, and
   Deligne's purity theorem, together with the six-operation fragment
   they require.

# Conventions

Throughout the blueprint: $`k = \Fq` is a finite field with $`q` elements,
$`F` denotes the *geometric* Frobenius (the inverse of the arithmetic
substitution $`a \mapsto a^q`), and $`F` acts on the Tate object
$`\Ql(1)` by $`q^{-1}`. Weights are always squared:
an element $`\alpha \in K^\times` is *pure of weight* $`w \in \ZZ` relative
to $`q` under an embedding $`\iota \colon K \to \CC` if
$`\|\iota\alpha\|^2 = q^{w}`. The reversed characteristic polynomial of an
automorphism $`u` is $`\charrev{u}`, with constant term $`1`; its
*reciprocal roots* are the eigenvalues of $`u`.

# How to read this blueprint

Each node records its *statement dependencies* (the `uses` of the statement
block: what is needed to even formulate the result) separately from its
*proof dependencies* (the `uses` of the attached proof block). Nodes linked
to a Lean declaration display its current status; nodes without a Lean link
have not yet been started. The final chapter assembles the main theorems; the
dependency graph and the progress summary are generated at the end of the
document.
