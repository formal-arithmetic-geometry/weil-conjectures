## Worker report

The module `lean/Sheaf/AlgebraicGeometry/HypersurfaceNonzeroRelativeDifferential.lean` defines `AlgebraicGeometry.Scheme.Hom.relativeDifferentialValue`, rendering the fibre value of the universal relative differential as `d a (z) ⊗ 1` in the tensor product of the stalk with the residue field. It states `smooth_zeroLocus_of_relativeDifferentialValue` with proof `sorry`.

The theorem uses `p : X ⟶ S` with `[Smooth p]`, an invertible module `M`, a global section `s : M.sections` (the sheaf global-section representation), a point `z` of the zero-locus subscheme, an open `U` containing its image, a free generator `e`, local coefficient `a`, the equation `s = a • e` on `U`, and the nonvanishing differential hypothesis. Its conclusion is an open neighbourhood `V` of `z` in the zero-locus whose composite to `S` is `Smooth`, exactly expressing smoothness of `Z → S` near `z`.

Dependency declarations used: `AlgebraicGeometry.Smooth` from `Mathlib.AlgebraicGeometry.Morphisms.Smooth`; `AlgebraicGeometry.Scheme.Modules.IsInvertible` from `WeilConjectures.AlgebraicGeometry.Modules.Invertible`; `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus` from `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`; `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` and `relativeDifferentialsDerivation` from `WeilConjectures.AlgebraicGeometry.Modules.Differentials`; `AlgebraicGeometry.Scheme.residueField` and `Scheme.residue` from Mathlib residue-field declarations. `def-weil-pbc-scheme-conventions` contributes conventions only and has no declaration to import.

Edge cases checked: the empty Jacobian row case is represented by the tensor definition without a dimension restriction; the zero differential fails the nonzero hypothesis; arbitrary open neighbourhoods and points are retained; no flatness assumption is introduced.

Searches made: `msearch.py` LeanFinder/LeanSearch/Loogle and grep searches for hypersurface, smooth quotient, Jacobian, and relative differential found no exact existing statement. Project searches over `WeilConjectures/` and `lean/Sheaf/` found no declaration of this node. The recorded stage-1 searches in the node likewise report no match.

## Second reading by Q138

Maintainer's independent second reading of immutable delivery
c2c9eb93bc4ce03b13e49a2e06454d5d62413b36, performed on 2026-10-18. I read the
item, all six statement-dependency records, the delivered module, and the actual
upstream declarations. The statement is correct. This replacement supplies the
reading missing from the original placeholder; it does not attribute that
reading to another Q138 worker.

Clause-by-clause match:

1. Schemes and smooth morphism: `{X S : Scheme.{u}} (p : X ⟶ S) [Smooth p]`.
   The convention node introduces no further object or standing hypothesis.
   The recorded Mathlib `Smooth` is affine-local ring-map smoothness, the
   equivalent notion cited in the dependency. Pass.
2. Invertible module and global section: `(M : X.Modules) [M.IsInvertible]
   (s : M.sections)`. This is `Scheme.Modules.IsInvertible`, not an unrelated
   invertibility predicate. Its local structure-sheaf isomorphisms give local
   rank one and quasi-coherence. `unitHomEquiv.symm s` is the corresponding map
   from the unit module; evaluation on one is the section. Pass.
3. Zero scheme and point: `Hom.zeroLocus (M.unitHomEquiv.symm s)` is the
   recorded actual ideal-sheaf construction, and `z` belongs to its
   `.subscheme`. It is not merely a topological zero set or an independently
   chosen subscheme. The unit module and M are invertible, as required by
   the zero-locus construction. Pass.
4. Trivializing neighbourhood: `U`, `hz`, `e`, and `he : IsFreeGenerator e`.
   The free-generator definition asserts bijectivity on every smaller open,
   precisely a sheaf trivialization, not just freeness of sections on U.
   No affine restriction on the given neighbourhood is imposed. Pass.
5. Local equation: `a : Γ(X, U)` and `ha` identify evaluation of the section
   map at one with `a • e`, exactly s = f in the chosen trivialization. Pass.
6. Nonvanishing: `relativeDifferentialValue` applies the universal relative
   derivation on U, takes its germ at the image of z, and forms its tensor
   with one over the ambient local ring. The residue-field module structure
   is obtained through the actual residue quotient map. Its body is `v ≠ 0`,
   with no arbitrary map or postponed data. It uses the ambient residue
   field, as in the statement; the closed immersion gives the same field
   as the point of the zero scheme. Pass.
7. Conclusion: the existential V is an open of the actual zero scheme,
   `z ∈ V`, and `Smooth (V.ι ≫ subschemeι ≫ p)` is smoothness on that
   neighbourhood over the original base. Pass.
8. No flatness assumption on the zero scheme, regular-section hypothesis,
   Noetherianity, finite-dimensionality, field base, or characteristic
   restriction appears. No conclusion asserting global smoothness is added.

Exact interfaces inspected: Mathlib `AlgebraicGeometry.Smooth` in
`Morphisms/Smooth.lean:62`; `Scheme.residueField` and `Scheme.residue` in
`ResidueField.lean:45,54`; upstream `Scheme.Modules.IsInvertible` in
`Modules/Invertible.lean:57`; `IsFreeGenerator` in `Modules/FreeGenerator.lean:100`;
`Hom.zeroLocusIdeal` and `Hom.zeroLocus` in `Modules/ZeroLocus.lean:159,178`;
`Scheme.Hom.relativeDifferentials` and `relativeDifferentialsDerivation` in
`Modules/Differentials.lean:93,99`. The explicit module-stalk scalar instance
in `Modules/FlatPullbackStalk.lean:185` justifies retaining that import.

Source check: read Stacks algebra.tex, definition-standard-smooth and
lemma-standard-smooth (Tags 00T6 and 00T7), especially smoothness and the last
n-c differential basis; morphisms.tex, lemma-smooth-locally-standard-smooth
(Tag 01V7) and lemma-differentials-affine (Tag 01UT); and divisors.tex,
definition-zero-scheme-s and lemma-zero-scheme (Tag 02OR). The node's enlarged
minor computation is valid: det enlarged J = det(J) b_j, nonvanishing finds
j > c, and adjoining t with tΔ-1 gives determinant Δ² after localization.
Thus no flatness of B is assumed. The replacement theorem docstring now
carries each of the six proof steps and their dependency ids.

One-definition search: independent rg searches in upstream WeilConjectures,
Mathlib AlgebraicGeometry, and the group's lean/Sheaf used
`cotangent.*(nonzero|non.zero)`, `differential.*hypersurface`,
`hypersurface.*smooth`, `zeroLocus.*smooth`, and `smooth.*zeroLocus`.
The group-scheme zero-locus affine-cover theorem concerns reduced finite-type
group schemes, not this assertion. Mathlib
`Algebra.IsStandardSmooth.of_basis_kaehlerDifferential` requires finite
presentation, vanishing H1 cotangent, and a differential basis; it does not
state this implication for a zero scheme. Existing smooth-locus/localization
results are likewise different. The delivered helper is the explicit
nonvanishing predicate built from the recorded notions, not a second
construction of any of those notions. Original recorded semantic searches
are retained in the node and worker report.

Edge cases: empty ambient or zero scheme has no z; s = 0 and a = 0 cannot
satisfy hda; an empty U is excluded only by hz, necessarily. For relative
rank zero (including n=c=0) the differential fibre is zero, so the hypothesis
is impossible. The case c=0 with positive relative rank uses the empty
minor equal to one. Nilpotents, nonreduced bases, all characteristics,
arbitrary/nonclosed points, and non-affine neighbourhoods remain admitted.
The universe u is arbitrary, and both schemes use the same universe as the
recorded Scheme morphism and differential APIs. No extra equality between
independent site or coefficient universes occurs.

Findings and changes: H8 in the original module: missing exact module
blueprint marker, missing source/blueprint on the helper, and no stepwise
proof docstring. These are replaced completely. H11 in the original report:
the second-reading section was explicitly only a placeholder; this section
supplies the independent reading. The original report also recorded no
per-file compiler command/result, so compiler evidence is supplied below.
Neither signature, the theorem body `by sorry`, the actual helper body, nor
any node field is changed. The item has exactly one theorem and one real
helper definition, both listed in lean.declarations. The lean.statement
field was checked byte-for-byte against both original and replacement
signatures, and agrees. No new node, dependency module, statement_change,
or citer audit is necessary.

Route pivot: no statement or proof dependency is on the current dropped-node
list, no route-pivot repair note exists for this item, and no dropped
infinity/dg/model machinery or pro-etale substitute is present.

## Compiler evidence

Independently ran:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q138 \
  lem-zl-hypersurface-nonzero-relative-differential \
  fixes/lean/Sheaf/AlgebraicGeometry/HypersurfaceNonzeroRelativeDifferential.lean
```

Exit code 0, with no Lean error or warning diagnostics. Final wrapper output:

```text
sandbox Sheaf/Stage2/Sandbox0.lean

(with the modules compiled into /dev/shm/nt-tmp/nt-local-compile-3gcnp5bp/.lbuild) [25.7 s]
library Sheaf/AlgebraicGeometry/HypersurfaceNonzeroRelativeDifferential.lean

[88.8 s]
```

The installed scompile.py currently forwards to the server's private side-overlay
compiler, rather than compiling on this machine; it was used as prescribed.
Its progress messages specify the 60-second limit after slot acquisition, and
nt_srv_compile.py invokes each `lc.run` with 60. The reported elapsed figures
above are transcribed exactly; no timeout or limit increase occurred.
The original and replacement modules are identical after removing comments,
so the successful compile verifies the delivered declaration signatures and
bodies as well as the final replacement. The original report contained no
recorded worker compile, and none is inferred here. No lake build, global
build, direct ssh, live Lean write, delivery, merge, or Git mutation was used.
