## Worker report

The module `Sheaf.AlgebraicGeometry.PseudoCoherentDistinguishedTriangle` states
`AlgebraicGeometry.Scheme.isPseudoCoherent_of_distinguished_triangle`, with proof `sorry`.
No definition is added and the node changes only in `lean`.

Hypothesis and conclusion correspondence:

- The scheme Y is `(Y : Scheme.{u})`.
- The category D(O_Y) is `schemeDerivedCategory Y`, on the recorded shared carrier
  `SheafOfModules.{u} (moduleRings Y.toRingedSpace)`.
- The triangle A → B → C → A[1] is `(T : Triangle (schemeDerivedCategory Y))`:
  its objects are `T.obj₁`, `T.obj₂`, `T.obj₃`, its arrows are `T.mor₁`, `T.mor₂`,
  `T.mor₃`, and the last arrow targets the shift of `T.obj₁` by integer 1.
- Distinguished is `(hT : T ∈ distTriang (schemeDerivedCategory Y))`.
- Pseudo-coherence of A and C is `(hA : IsPseudoCoherent Y T.obj₁)` and
  `(hC : IsPseudoCoherent Y T.obj₃)`.
- The conclusion is `IsPseudoCoherent Y T.obj₂`, pseudo-coherence of B.
- The two `HasDerivedCategory.{w}` instance binders are the localization choices required
  by the recorded definitions, on Y and its open localized sites. They fix the size
  convention and let the very same predicate be applied to all three objects; they add
  no geometric finiteness, separatedness, Noetherian or boundedness hypothesis.
  Every universe and variable is explicitly bound.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (and `Scheme.Hom` read),
  the scheme and its morphisms, node `def-pc-scheme`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`,
  node `def-pc-derived-category`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, its triangulated
  instances, and `DerivedCategory.mem_distTriang_iff`, node
  `def-weil-abstract-derived-category` (Mathlib leaf).
- `Sheaf.AlgebraicGeometry.PseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsPseudoCoherent`, node `def-pur-pseudo-coherent-complex`.

The only direct import is the pseudo-coherent definition module, which supplies all the
other dependencies transitively. The theorem docstring carries all three DAG proof steps
with the named proof dependencies for stage 3.

Edge cases checked before writing: the empty scheme gives a vacuous local predicate for
all three objects; zero objects admit the zero finite-free model; identity/zero
triangles give the expected closure statement. No rank positivity, global upper bound,
nonempty open cover, affine, Noetherian or characteristic assumption is imposed.
The conclusion concerns all objects of D(O_Y), not an independently assumed D_QCoh
subcategory. The common localization universe w is the one required by the dependency.

Searches for an existing statement:

- `msearch.py ... leanfinder "pseudo-coherent complexes are closed under distinguished
  triangles"`: eight generic hits including `DerivedCategory.mem_distTriang_iff` and
  `DerivedCategory.triangleOfSES_distinguished`; no pseudo-coherence theorem.
- `msearch.py ... loogle "DerivedCategory, PseudoCoherent"`: zero hits, unknown identifier
  `PseudoCoherent`.
- `msearch.py ... grep "pseudo.?coherent|PseudoCoherent"`: zero Mathlib hits.
- `rg -n 'PseudoCoherent|pseudo.?coherent'` in the source `WeilConjectures`: only a
  prose reference in `AlgebraicGeometry/Cohomology/DirectImage.lean`, no declaration.
- The same search in `lean/Sheaf` finds the scheme predicate and several ring-specific
  statements, including `CategoryTheory.isMPseudoCoherent_of_distinguished_triangle`;
  the latter concerns ModuleCat R and fixed m, not the scheme statement here.
- `grep -rn 'lem-pc-pseudo-coherent-distinguished-triangle'` in `WeilConjectures`: no hits.
- `rg -n 'isPseudoCoherent_of_distinguished_triangle'` in Mathlib, source,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no name collision.

Source checked: the local Stacks TeX file is absent on this machine, so I opened
[Stacks Tag 08CD](https://stacks.math.columbia.edu/tag/08CD). Its part (2) is the
first-and-third to middle implication for m-pseudo-coherence; applying it for every m
is precisely this node. No statement fault or correction is needed.

Validation: `scompile.py` compiled the module cleanly on the server in 2.1 seconds
(exit code 0, no warnings). `deliver2.py --no-push` printed OK: compilation and preflight
passed except for the independent second-reading section, which the second reader writes.
Nothing was pushed.

## Second reading by C1

I independently opened the item node, its delivered module, all four statement-dependency
nodes and their recorded declarations. No mathematical mismatch was found. The Lean file
and node record are unchanged; this second-reading record is the only delivery repair.
The recorded `lean.statement` is byte-for-byte the theorem signature before `:= by`.

Object/hypothesis/conclusion checklist (each verdict: exact):

1. Arbitrary scheme Y: `(Y : Scheme.{u})`, using Mathlib's `Scheme` structure extending
   `LocallyRingedSpace` with local affine charts. I read `Scheme` and `Scheme.Hom` in
   `Mathlib/AlgebraicGeometry/Scheme.lean`, lines 42 and 74. No field or base is fixed.
2. D(O_Y): `schemeDerivedCategory Y`, the abbreviation of
   `DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace))` in the recorded
   `Sheaf.AlgebraicGeometry.DerivedCategory`. This is the category of all derived objects,
   without an extra D_QCoh or boundedness restriction. Its abelian instance is shared.
3. A, B, C and all three arrows: `(T : Triangle (schemeDerivedCategory Y))`, with
   `A = T.obj₁`, `B = T.obj₂`, `C = T.obj₃` and `T.mor₁`, `T.mor₂`, `T.mor₃`.
   I opened Mathlib's `CategoryTheory/Triangulated/Basic.lean`: `Triangle.mor₃` has
   target `T.obj₁⟦(1 : ℤ)⟧`, exactly A[1]. Bundling preserves the object/arrow quantifiers.
4. Distinguished: `(hT : T ∈ distTriang (schemeDerivedCategory Y))`.
   I read `DerivedCategory` and `Q`, their localization and triangulated instances, and
   `DerivedCategory.mem_distTriang_iff` in Mathlib's derived-category `Basic.lean`.
   Distinguished means isomorphic to the image of a cochain-complex cone triangle,
   as `def-weil-abstract-derived-category` requires.
5. A pseudo-coherent: `(hA : IsPseudoCoherent Y T.obj₁)`.
6. C pseudo-coherent: `(hC : IsPseudoCoherent Y T.obj₃)`.
   For both I opened `def-pur-pseudo-coherent-complex` and its recorded
   `Scheme.IsPseudoCoherent` definition in `PseudoCoherentComplex.lean`. It quantifies
   over every point, a containing open, a bounded-above cochain complex of finite-free
   module sheaves, and an isomorphism to the derived restriction. It uses the same
   carrier and localization as D(O_Y); there is no private ring-complex predicate.
7. Sole conclusion, B pseudo-coherent: `IsPseudoCoherent Y T.obj₂`, using that same
   definition. Neither another two-out-of-three clause nor a stronger bound is asserted.
8. Size infrastructure: `universe u w` and the two `HasDerivedCategory.{w}` binders
   are exactly the parameters of the recorded derived category and local predicate.
   I read `HasDerivedCategory` as chosen localization with morphisms in `Type w`, and
   `HasDerivedCategory.standard` in Mathlib. These allow chosen localizations on Y and
   every open in a common sufficiently large universe; no scheme is excluded and no
   geometric assumption is added. All universes and variables are explicitly bound.

Source reading: local Stacks TeX is absent. I fetched and read the actual
[cohomology.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/cohomology.tex)
section `section-pseudo-coherent`, definition `definition-pseudo-coherent`, and the
statement and proof of `lemma-cone-pseudo-coherent`. The section has no standing
Noetherian, quasi-compact, separated or characteristic assumption. Its lemma assumes
only a ringed space, an integer m and a distinguished triangle. Part (2), for every m,
gives exactly the node's scheme specialization. I also opened
[08CD](https://stacks.math.columbia.edu/tag/08CD),
[08CB](https://stacks.math.columbia.edu/tag/08CB), and
[08E7](https://stacks.math.columbia.edu/tag/08E7) to check the source statement and
scheme/ring interpretation of the dependency predicate.

Edge cases: the empty scheme is permitted (`∀ y` in the local predicate is vacuous);
no nonempty-cover assumption is present. Zero objects and zero ranks are permitted,
since the witness rank is `r : ℕ` and `Fin 0` is allowed. Degree zero and all negative
degrees are included through `ℤ`; there is no selected n or excluded n = 0 case.
There is no index set in this theorem. The local upper bound may vary with the point
and the degreewise finite rank may vary with degree, so non-quasi-compact schemes and
objects without a global upper bound are covered. Arbitrary residue characteristics,
non-Noetherian schemes and arbitrary scheme universes u are allowed. Identity and
zero triangles introduce no additional restrictions.

Independent searches (using different terms from the first reader):

- LeanFinder: `extension closure of locally bounded above finite free complexes on
  schemes`: eight unrelated finite-type/sheaf finite-type results; no theorem here.
- Loogle: `Triangle, distTriang`: parse error, no usable results; this failure is
  recorded rather than treated as evidence of absence. The successful LeanFinder and
  textual searches provide the substantive independent evidence.
- Mathlib grep: `coherent.*triangle|triangle.*coherent|PseudoCoherent|pseudoCoherent`:
  zero hits.
- LeanSearch: `pseudo coherence of the middle term of a distinguished triangle of
  sheaves`: service unavailable (Internal Server Error), recorded without a verdict.
- Independent `rg -i` of source `WeilConjectures` and project `lean/Sheaf` for
  `pseudocoherent|pseudo.?coherent|coherent.*triangle|triangle.*coherent`: source has
  only the DirectImage prose mention; project has the shared scheme definition and
  ring-specific results. I opened the ring distinguished-triangle theorem: it is for
  `DerivedCategory (ModuleCat R)` and fixed m, not this scheme statement. No duplicate.
- Exact theorem-name search in Mathlib, source, project and `dag/lean_names_upstream.json`
  found no collision.

H5/H6/H8/H9: no definitions are delivered, so no hollow definition occurs. The sole
proof is `by sorry`. Module and theorem docstrings name Tag 08CD and the exact blueprint
id. The theorem docstring follows all three node proof steps: common local affine
models; rotation, affine equivalence and K-projective chain-map lift; finite-free cone
and comparison of third terms. Imports use the recorded predicate module, which
supplies the other dependencies transitively. All Lean lines are at most 100 characters.
No new definition node, dependency module or statement correction is needed.

Validation: independent `scompile.py C1 lem-pc-pseudo-coherent-distinguished-triangle`
compiled the delivered module on the server in 2.1 seconds, exit 0, with no warnings.
