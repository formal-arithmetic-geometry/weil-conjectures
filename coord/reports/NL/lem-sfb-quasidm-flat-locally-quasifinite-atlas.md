## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiDmFlatLocallyQuasiFiniteAtlas` states
`CategoryTheory.locallyQuasiFiniteModuliDiagonal_iff_flatLocallyQuasiFiniteAtlas`.
It formalizes Tag 06MF (theorem-quasi-DM), relative over a scheme `S`, using the
existing project predicates for algebraic stacks, representability by algebraic
spaces, field-extension surjectivity, flatness, local finite presentation, and
chartwise local quasi-finiteness.

The hypothesis `S` is the explicit scheme binder `{S : Scheme.{u}}`; `F` is the
based category over `S`; and `hF : IsAlgebraicModuliStack F` renders the phrase
“Let `F` be an algebraic stack”. The left-hand clause
`ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite
(moduliRelativeDiagonal (moduliBaseStructure F))` is local quasi-finiteness of the
relative diagonal, tested on every scheme 2-base change and every etale scheme
chart. The right-hand existential introduces a scheme `W : Over S` and a map
`q : BasedFunctor (discreteModuli (yoneda.obj W)) F`; its five conjuncts render,
respectively, that `q` is representable by algebraic spaces, surjective by field
extension and a vertical 2-isomorphism, flat on all charts, locally of finite
presentation on all charts, and locally quasi-finite on all charts. No
separatedness, quasi-compactness, Noetherianity, or finite-inertia hypothesis is
added.

The statement dependencies used are: `AlgebraicModuliStack` for
`CategoryTheory.IsAlgebraicModuliStack`; `StablePointedModuliGroupoids` for
`BasedCategory`, `Over`, `discreteModuli`, `BasedFunctor`, `yoneda`, and
`moduliRelativeDiagonal`'s ambient constructions; `DmStackMorphismProperties`
for `ModuliSpaceTest` and `IsRepresentableByAlgebraicSpaces`; `RelativeModuliInertia`
for `moduliBaseStructure`; `StackChartwiseSmoothEtaleCalculus` for
`IsSurjectiveModuliMap`, owned by `def-sfb-surjective-moduli-map`; `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`
for `Scheme.Hom.IsLocallyQuasiFinite`; and Mathlib's
`AlgebraicGeometry.Flat` and `AlgebraicGeometry.LocallyOfFinitePresentation`.
Proof-dependency modules are imported where their declarations are already
available: `RepresentableLocallyQuasiFiniteCalculus`, `AlgebraicStackFibreProducts`,
`LocallyQuasiFiniteRelativeDimension`, and `FieldGroupoidStabilizerDimension`.

The six proof steps in the theorem docstring follow Tag 06MF: descent from an
atlas, the closed smooth chart, the stabilizer and dimension-zero fibre, the
regular slice, the fibre neighbourhood, and the coproduct of local charts. The
proof is deliberately `sorry` as required for stage 2.

Edge cases checked against the source statement are the empty stack (empty
coproduct atlas), arbitrary base scheme without Noetherian or separatedness
assumptions, and absence of quasi-compactness and finite-inertia assumptions.
The quantification over `W` permits the empty scheme. The `ModuliSpaceTest`
predicates quantify over every scheme test and etale chart, including empty
charts, while `IsSurjectiveModuliMap` retains field-extension lifting rather than
requiring a pointwise section.

Searches for an existing declaration were made with:

- `msearch.py ... leanfinder "An algebraic stack has locally quasi-finite diagonal if and only if it has a surjective flat locally finitely presented locally quasi-finite scheme atlas"`: scheme-only hits (`LocallyQuasiFinite`, diagonal properties); no stack theorem.
- `msearch.py ... leansearch "A quasi Deligne Mumford algebraic stack has a surjective flat locally finitely presented locally quasi finite scheme atlas"`: eight scheme-level hits; no matching stack-level declaration.
- `msearch.py ... loogle '"AlgebraicStack", "Flat"'`: zero hits.
- `msearch.py ... grep 'quasi.?DM|AlgebraicStack|stack.*atlas'`: zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf`: no declaration for this equivalence; nearby declarations are the component predicates and unrelated DM atlas theorems.

The existing landed nodes `def-sfb-dm-stack-morphism-properties`,
`def-sfb-relative-moduli-inertia`, and `def-sfb-surjective-moduli-map`
are added to `stmt_deps` to record the three reused interfaces. They were already
landed and no new declaration or dependency-module repair was necessary.

No statement correction or dependency module was needed. No `STATEMENT-DISPUTED`
flag applies. The file compiles cleanly with the prescribed `scompile.py` command;
the only postponed proof is the named theorem above.

## Second reading by NL

This is a second self-reading; the maintainer supplies the independent review.
I reopened the node and the module. The explicit `hF` hypothesis is exactly the
node's algebraic-stack premise. The left side uses the structural relative
moduli diagonal and the existing chartwise `ModuliSpaceTest` local
quasi-finiteness predicate. On the right, `W` is a scheme over `S`, `q` is its
actual map into `F`, and each conjunct corresponds in order to representability,
field-extension surjectivity, flatness, local finite presentation, and local
quasi-finiteness. I found no extra separatedness, quasi-compactness,
Noetherianity, or finite-inertia condition and no omitted clause. The empty-stack
case remains expressible by the existential over `W`; all field and scheme
universes are explicit.

## Returned delivery repair

H2, immutable returned head `3d0db828e1f0`: replaced the added statement
dependency `lem-sfb-stack-chartwise-smooth-etale-calculus` by the now-landed
definition node `def-sfb-surjective-moduli-map`. Its `existing: true` Lean record
names precisely `CategoryTheory.IsSurjectiveModuliMap` in
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`; I read that
definition and its full signature again. This predicate is the declaration used
in the atlas conclusion. No theorem conclusion from that module supplies
statement data; the calculus theorem remains a proof dependency.

Compared the retained sandbox node with current main: apart from `lean`, the
only additions are the three used definition nodes
`def-sfb-dm-stack-morphism-properties`, `def-sfb-relative-moduli-inertia`, and
`def-sfb-surjective-moduli-map`. The Lean source, imports, signature, and
docstrings are unchanged from the returned delivery. The prescribed delivery
wrapper refreshes and rebases the delivery onto current main, which contains
the new surjectivity definition node.

Repair second self-reading: confirmed all five atlas conjuncts and the relative
diagonal clause are identical to the independently checked returned theorem.
Only dependency ownership was corrected, as requested; no mathematical
statement correction was needed. Recompile and delivery preflight are run again
for this repair.
