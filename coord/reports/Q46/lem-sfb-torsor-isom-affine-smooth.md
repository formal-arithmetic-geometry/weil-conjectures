## Worker report

The module `Sheaf.AlgebraicGeometry.TorsorIsomAffineSmooth` states
`AlgebraicGeometry.RepresentedRightTorsor.isom_affine_smooth`, with one `sorry`.
It also implements the two pieces of notation introduced by this very node:
`EquivariantIsom` is its set I(T), and `testChangeMap` is the canonical map between
its specified fibre products under a map of test schemes. These are concrete
structures/maps, with no postponed data or helper theorem. No node correction,
new independent notion, or dependency repair is needed.

Hypothesis-by-hypothesis and clause-by-clause comparison:

- Arbitrary schemes B,Y and Y -> B: `{B : Scheme.{u}}` and `Y : Over B`.
  An object `T : Over Y` here is in the category `Over (Over B)`: its underlying
  B-scheme is `T.left` and its Y-map is `T.hom`. This is precisely a Y-scheme,
  with its forced B-structure. Likewise `I : Over Y` is a Y-scheme and its actual
  structure morphism of schemes is `I.hom.left`.
- A group scheme over B with its multiplication, identity and inverse diagrams:
  `H : Grp (Over B)`. The dependency's `GrpObj` is the unbundled structure used
  by this bundled Mathlib group object; it is available over every scheme B,
  without a field hypothesis. The item expressly says to use base B.
- H -> B affine and smooth: `[IsAffineHom H.X.hom] [Smooth H.X.hom]`.
- P,Q represented right H-torsors over Y: `(P Q : RepresentedRightTorsor H Y)`.
  This is the recorded dependency definition, including actual right actions,
  their unit and multiplication laws, the cartesian torsor square, flatness,
  surjectivity, locally finite presentation, quasi-compactness and
  quasi-separatedness. No local or global section is assumed.
- P_T and Q_T are the actual `pullback P.projection T.hom` and
  `pullback Q.projection T.hom` in schemes over B. The forgetful functor creates
  these pullbacks, so they are the node's scheme fibre products. Their projections
  are Mathlib's `pullback.fst` and `pullback.snd`.
- I(T) consists of T-scheme isomorphisms: `EquivariantIsom.iso` is an actual
  scheme isomorphism over B; `over_base` says its composite with the Q_T -> T
  projection is the P_T -> T projection. Its inverse is consequently over T too.
- Commutation with the right H_T-action: `equivariant` tests every B-scheme U,
  every two U-points p,p' of P_T, and every U-point g of H. The first premise says
  the P-coordinate of p' is the action of g on the P-coordinate of p. The second
  premise says p' has the same T-coordinate. Thus p' is exactly p*g. The conclusion
  says the Q-coordinate of its image is the action of g on the Q-coordinate of
  the image of p. Since `over_base` already fixes the T-coordinate, this is full
  equivariance, not just an equation on one projection. Such p' exists uniquely:
  the torsor square makes the original action preserve the Y-projection, and
  the pullback universal property then supplies p'. For fixed U -> T, a U-point
  of H is exactly a U-point of H_T, explaining the H_T formulation without
  duplicating a group base-change or action definition.
- Representability on every test scheme: `∃ I : Over Y` and
  `∃ E : ∀ T : Over Y, (T ⟶ I) ≃ EquivariantIsom P Q T.hom`.
  `Equiv` gives both directions and both inverse laws, without selecting a
  merely nonempty model for the functor.
- Pullback restrictions and naturality: the equation following E is the commuting
  square `(E T' (h ≫ s)).iso.hom ≫ testChangeMap Q h =
  testChangeMap P h ≫ (E T s).iso.hom` for every `h : T' ⟶ T` and `s : T ⟶ I`.
  The canonical maps are `pullback.map` with identity on P (respectively Q), h
  on the test scheme, and identity on Y. This square uniquely characterizes
  pullback of the isomorphism. Since `EquivariantIsom` has only an isomorphism
  and proposition fields, there is no extra choice of equivariance data for
  naturality to forget. This includes identity and composite restrictions.
- I -> Y affine and smooth: `IsAffineHom I.hom.left ∧ Smooth I.hom.left`.
- Affine Y implies affine I: `(IsAffine Y.left → IsAffine I.left.left)`.
- The final no-extra-assumptions sentence is respected: there are no field,
  triviality, connectedness, commutativity, or reductivity binders.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`, `IsAffine`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, bundled `Grp`.
- `Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`:
  `AlgebraicGeometry.RepresentedRightTorsor`, including all its fields. Its
  split-solvability definitions are not used or imposed.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.map`.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: the over-category framework.

The available proof-dependency modules are imported with ordinary `import`:
Mathlib's `Sites.Fpqc` (fppf/fpqc covers and covering axioms),
`Morphisms.LocalFlatDescent` (smooth fpqc descent), `Morphisms.Proper`
(proper base change; the relevant smooth base-change declaration is in the public
Smooth import), `Morphisms.QuasiCompact` (quasi-compact base change),
`WeilConjectures.AlgebraicGeometry.AffineFpqcDescent`,
`WeilConjectures.AlgebraicGeometry.FpqcMorphismsDescend`, and
`Sheaf.AlgebraicGeometry.FpqcAffineDescent`.
The theorem docstring carries all six proof steps, including the noncommutative
transition c_2=b^{-1}c_1a, full descent of maps/inverses/equivariance, naturality,
and the two separate smooth-descent applications.

Edge cases checked mathematically before writing: empty Y (all tests over Y are
empty and the empty I represents the functor); empty B; the trivial group; P=Q
without a global section; noncommutative H (no interchange of a,b,c); nonreduced
base; identity and arbitrary test maps; and affine Y including the zero-ring
spectrum. No nonemptiness, finite type of Y/B, or field condition occurs. The
single universe u is the ordinary category of schemes in an arbitrary fixed
universe, shared with the recorded torsor interface; all U and all T in that
category are quantified, rather than a smaller universe of tests.

Searches (2026-10-24):

- `msearch.py ... leanfinder "The equivariant isomorphism functor of two
  represented right torsors under an affine smooth group scheme is represented
  by an affine smooth scheme"`: eight hits, all affine-space definitions and
  Hom/coordinate equivalences; none is the asserted torsor theorem.
- `msearch.py ... loogle '"Torsor", "Scheme"'`: zero hits.
- `msearch.py ... grep 'Isom.*Torsor|Torsor.*Isom|isom.*torsor|torsor.*isom'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` for torsor/isomorphism and `RepresentedRightTorsor` in both
  `lean/WeilConjectures` and `lean/Sheaf`: existing results concern finite
  constant etale torsors, module trivialization torsors, or specialized additive
  and torus torsors, not this represented right-torsor Isom theorem. The exact
  recorded represented-torsor structure was found and reused.
- `grep -rn 'lem-sfb-torsor-isom-affine-smooth' lean/WeilConjectures`:
  no existing declaration attached to this item.

Source checks: read Stacks groupoids.tex Tag 049C (affine torsor representability),
descent.tex Tags 0245 (affine effective descent), 02W0 (fully faithful morphism
descent), 02L5 (affineness fpqc-local) and 02VL (smoothness fpqc-local). The node
already gives the explicit simultaneous-trivialization Isom variant of these
results. Its proof and statement do not need correction.

Validation: the first prescribed server compilation succeeded except for one
unnecessary-simpa linter warning in `testChangeMap`. Replaced that proof by
`by simp`; a fresh compile is used for the final validation. No proofs are
supplied beyond definitional commutative-square witnesses; the only theorem
proof is `sorry`.

## Second reading by Q46

I reread the node and the finished file against each other after compilation.
This is a self-check: the dispatcher explicitly prohibits starting another agent;
the maintainer's independent reading remains the independent review. In
particular I checked that the nested `Over Y` is taken with Y in `Over B`, so its
objects impose no extra structure; that `iso` is an actual fibre-product
isomorphism, not an equivalence on global points; that the two premises of
`equivariant` describe the actual right translate and do not omit H_T-points;
that `over_base` supplies the other coordinate of equivariance; and that
naturality is equality of full morphisms on the pulled-back torsors. Affine and
smooth conclusions apply to the actual map I -> Y, while the affine-base clause
applies to the underlying scheme I. No mismatch or statement change was found.
The proof plan retains all six steps, including quasi-compactness checks before
the two smooth-descent steps. No new nodes or dependency modules are present.

## Retry validation (2026-10-24)

Retained the saved packet and first ran the required
`deliver2.py Q46 lem-sfb-torsor-isom-affine-smooth --no-push`.
The server compile failed before Lean diagnostics with
`resource exhausted (error code: 28, no space left on device)`.
A direct prescribed `scompile.py` invocation for the saved module reproduced
the identical server failure. Neither command pushed anything. The packet
is retained; server storage must be restored before validation can complete.

## Successful retry validation (2026-10-24)

The required first dry run on the retained packet now passes:
`deliver2.py Q46 lem-sfb-torsor-isom-affine-smooth --no-push`
reported `OK (dry run): commit b61e05d6f8b passes the preflight and compiles;
nothing pushed`. Both sandbox and library-path compilations completed under the
prescribed 60-second limits. The previous server-storage failure is resolved.

Reread the saved module, the current item statement and all six current
statement-dependency records, and the actual represented-torsor structure.
Confirmed the arbitrary-base group object has no field hypothesis; its bundled
`Grp` contains exactly the recorded `GrpObj` structure. The torsor interface
retains flatness, surjectivity, finite presentation, both action laws and the
cartesian torsor square. Rechecked the T-coordinate condition and the
all-test-scheme action equation in `EquivariantIsom`, and the full-morphism
naturality square in the theorem. They render equivariant T-isomorphisms and
pullback restriction exactly. No hypothesis or conclusion mismatch was found.
The saved node differs from the current repository node only in `lean`, and its
recorded statement equals the theorem signature verbatim. No Lean or node
changes were needed; the delivered theorem remains a stage-2 statement with
`sorry`, with the two helpers supplying concrete data.
