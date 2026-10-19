## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceOpenImmersionEtaleLocal` states
`AlgebraicGeometry.AlgebraicSpace.isOpenImmersion_of_etale_cover`. It uses the
recorded algebraic-space encoding from `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
`X` and `P` are objects of `AlgebraicSpace S`, and `a : X ⟶ P` is their
morphism. A family of target scheme maps is represented by `I : Type u`,
`P_i : I → Over S`, and maps `p_i : yoneda.obj (P_i i) ⟶ P.obj.obj`.

The hypothesis `h_etale` says each family map is `AlgebraicSpace.IsEtale`.
The hypothesis `h_joint` renders joint surjectivity on the fppf site: for every
scheme test `T : Over S` and section `x` of `P` over `T`, there is an fppf
covering sieve `R` of the underlying scheme `T.left` such that each arrow
`f : U ⟶ T` in the sieve admits an index `i` and a section of `P_i` over `U`
whose image under `p_i` is the restriction of `x` along `f`. This includes
arbitrary (including empty) index types and uses the fppf-local meaning of a
jointly surjective family.

For each `i`, `h_open` applies `AlgebraicSpace.IsRepresentableWith` to the
canonical pullback projection
`pullback.snd a.hom.hom (p_i i)`. Its property predicate is
`fun _ _ q => IsOpenImmersion q.left`, so every scheme test of the base change
is represented by a scheme morphism that is an open immersion. The conclusion
is the same representability-with-open-immersion predicate for `a.hom.hom`,
which is exactly representability of `a` and openness after every scheme test.
The source's final scheme case is the specialization to a represented target:
taking the target itself as the scheme test gives the asserted scheme open
subscheme.

Dependency declarations used:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` (scheme objects and
  `Over S` scheme morphisms).
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  declarations `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`/`IsEtale`.
- `def-weil-open-immersion`: Mathlib
  `AlgebraicGeometry.IsOpenImmersion`.

Edge cases checked: `I` is an unrestricted `Type u`, so empty and infinite
families are admitted; no nonemptiness or finiteness hypothesis is introduced.
The fppf covering sieve is allowed to be any covering (including the empty
cover where the test is empty), and no nonempty or quasi-compact assumption is
added to scheme tests. The predicate is the full Mathlib open-immersion
predicate, so empty schemes and identity open immersions are included.

Searches made:

- `msearch.py ... leanfinder "An algebraic space mapping to a scheme becomes an
  open subscheme if the morphism is an open immersion after etale base change"`:
  eight hits, all schemes/presheafed spaces; no algebraic-space descent theorem.
- `msearch.py ... leansearch` with the same query: eight hits, including
  `AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange`, but no theorem
  about algebraic-space representability or etale descent.
- `msearch.py ... loogle "AlgebraicSpace, IsOpenImmersion"`: zero hits.
- `msearch.py ... grep "AlgebraicSpace|algebraic.space"`: zero hits in the
  searched Mathlib subdirectory.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for algebraic-space open
  immersion/descent names: no existing declaration matching this statement.

No statement correction, dependency repair, or new node was needed. The file
compiles cleanly with `scompile.py`; the theorem proof is intentionally `sorry`
for stage 2.

## Repair self-check

This packet repairs the returned delivery by retaining the reviewed module and
node statement, rerunning the required `deliver2.py --no-push` preflight, and
recording the successful clean compile and preflight on the retained content.
The returned head `30bcc36de45b` was inspected; the sandbox packet is the same
mathematical statement and module, with this report update making the repair
delivery distinct from an unchanged re-push.

## Second reading by Q99

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
