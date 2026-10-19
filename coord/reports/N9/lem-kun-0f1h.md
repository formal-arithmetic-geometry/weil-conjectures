## Worker report

Recovery note: the retained sandbox contained only launcher marker files. There was
no earlier Lean module, node copy, report, or second-reading section to preserve.
This packet was reconstructed from the unchanged DAG node and its source. The
review below records the actual source and interface checks; it does not claim
that a missing first-worker artifact was available for comparison.

The delivery states `AlgebraicGeometry.Etale.isIso_openProductExchange` in
`Sheaf.AlgebraicGeometry.OpenProductExchange`, with its whole proof `sorry`.
It asserts exactly Stacks Tag 0F1H, `lemma-kunneth-localize-on-X`, read in
`literature/stacks-project/etale-cohomology.tex`, lines 20402–20595.
The complete ten-step DAG proof is included in the theorem docstring, retaining
all cited nodes and the coefficient, comparison, and closed-support arguments.
No proof, new definition, new node, or dependency repair is delivered.

The field is `(K : Type u) [Field K]`; the three K-schemes are
`U X Y : Over (Spec (.of K))`; the K-morphism is `j : U ⟶ X`;
`[IsOpenImmersion j.left]` is the open-immersion hypothesis. Finite type of each
structure map is its pair `[LocallyOfFiniteType T.hom] [QuasiCompact T.hom]`.
The coefficient is `F : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}`.
The stalk condition is `hF : IsTorsionOfInvertibleOrder K U F`.
The conclusion is `IsIso (openProductExchange j Y F)`.

Dependencies read at their definitions:

- `Mathlib.Algebra.Field.Defs`: `Field` extends `CommRing` and `DivisionRing`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` is the locally
  ringed-space open-immersion property, not merely an open map.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact` give the node's finite type.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, and `pullback.snd` are the chosen categorical fibre product.
- `Mathlib.CategoryTheory.Sites.Sheaf` and `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `Sheaf T.smallEtaleTopology AddCommGrpCat` is the abelian étale sheaf category.
- `Mathlib.AlgebraicGeometry.Sites.EtalePoint` and
  `Mathlib.CategoryTheory.Sites.Point.Basic`: `Scheme.pointSmallEtale` and
  `Point.sheafFiber` give the pointed-neighbourhood geometric stalk.
- `Sheaf.AlgebraicGeometry.InvertibleTorsionOrders`:
  `Etale.IsTorsionOfInvertibleOrder` quantifies over each separably closed
  geometric point and each stalk element, requiring a positive natural number
  `n`, `(n : K) ≠ 0`, and `n • x = 0`. No common annihilator is required.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`:
  `Etale.exactDerivedBaseChangeMap` is the mate of the canonical descended
  inverse-image square under the exact inverse-image/derived-direct-image
  adjunctions. It has actual data, not a chosen arbitrary map.
- `Sheaf.AlgebraicGeometry.OpenExchangeSeparableClosureReduction`:
  `Etale.openProductExchange` applies that same exchange to the canonical
  pullback square and to `DerivedCategory.singleFunctor _ 0` of `F`.
  Its existing owner `lem-kun-0f1h-sep-reduction` is added to `stmt_deps`,
  as permitted for a landed interface; its theorem is also a proof dependency.

All recorded statement and proof dependency modules are imported. Three recorded
proof module sources were absent in the older local checkout; their current
server sources were read with `scompile.py --source`:
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations`, and
`Sheaf.AlgebraicGeometry.DerivedModuleUnderlyingComparison`. They exist on the
current compilation side and require no duplicate module in this packet.

Searches (2026-10-17):

- LeanFinder via `msearch.py`: “etale cohomology open immersion base change
  product field torsion invertible” returned eight unrelated algebraic
  étaleness/open-immersion facts, no matching exchange theorem.
- Loogle via `msearch.py`: `"openProductExchange"` returned zero results.
- LeanSearch via `msearch.py`: “For an open immersion of finite type schemes over
  a field the derived direct image commutes with product base change for prime
  to characteristic torsion abelian sheaves” returned eight open-immersion,
  quasi-coherent-module stalk, and étaleness results, no match.
- `rg` independently searched Mathlib, upstream `WeilConjectures`, and project
  `lean/Sheaf` for `openProductExchange`, `kunneth.localize`, `0F1H`, and for
  open-immersion base-change names. The existing product map and the conditional
  separable-closure reduction were the relevant matches. Proper base-change,
  smooth base-change, and clopen base-change results have different hypotheses.
  `dag/lean_names_upstream.json` had no exact match. The proposed full theorem
  name does not occur in Mathlib, upstream, or the existing project library.

The edge-case review and hypothesis-by-hypothesis verdict are recorded below.

## Second reading by N9

Read the source statement first: Stacks Tag 0F1H introduces an arbitrary field,
an open immersion of finite-type K-schemes, an arbitrary finite-type K-scheme Y,
and an abelian sheaf on U with stalkwise torsion orders invertible in K. It
asserts that the canonical derived exchange is an isomorphism. No surrounding
assumption of algebraic or separable closure, separatedness, properness,
projectivity, characteristic, fixed annihilator, or nonemptiness applies to this
statement. Separably closed K and projective Y occur only in its proof reductions.
The DAG statement agrees with the source; no statement correction is needed.

Object/hypothesis/conclusion inventory, matched against the delivered signature:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary field K | `(K : Type u) [Field K]` | Exact; no closure or characteristic assumption. |
| Schemes U, X, Y over K | `(U X Y : Over (Spec (.of K)))` | Exact bundled schemes and structure maps. |
| A K-morphism j : U → X | `(j : U ⟶ X)` | Exact; `Over` includes the structure-map triangle. |
| j is an open immersion | `[IsOpenImmersion j.left]` | Exact Mathlib notion from the recorded dependency. |
| U is finite type over K | `[LocallyOfFiniteType U.hom] [QuasiCompact U.hom]` | Exact finite type, neither separated nor affine assumed. |
| X is finite type over K | `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` | Exact same conjunction. |
| Y is finite type over K | `[LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]` | Exact same conjunction. |
| Z = Y ×_K X and q : Z → X | `pullback Y.hom X.hom` and `pullback.snd Y.hom X.hom` inside `openProductExchange` | Exact chosen fibre product and projection. |
| V = Y ×_K U with maps p to U and h to Z | `pullback j.left q`, with `pullback.fst j.left q` and `pullback.snd j.left q` | Canonically the same product by the universal property, using `j.w`; first projection is p and second is h. |
| An arbitrary abelian étale sheaf F on U | `(F : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1})` | Exact coefficient category; no module structure or constructibility assumed. |
| Every stalk element has torsion order invertible in K | `(hF : IsTorsionOfInvertibleOrder K U F)` | Exact elementwise positive annihilator, allowed to vary with both point and element. |
| Exchange on F considered in degree zero | `openProductExchange` evaluates `exactDerivedBaseChangeMap` at `DerivedCategory.singleFunctor _ 0` of F | Exact unbounded canonical mate, not a cohomology-only assertion. |
| q⁻¹ Rj_* F → Rh_* p⁻¹ F is an isomorphism | `IsIso (openProductExchange j Y F)` | Exact entire morphism; no converse or added conclusion. |

Checked the helper itself with the file open. Its `IsPullback.of_hasPullback
j.left q` has corners V,U,Z,X, maps p,h,j,q in exactly the order expected by
`CommSq` and `exactDerivedBaseChangeMap`. The chosen square is therefore cartesian
by construction. `exactDerivedBaseChangeMap` is defined by `mateEquiv`, using the
canonical derived adjunctions and the functorially descended square comparison.
Its source and target are respectively `D(q⁻¹)(Rj_*(F[0]))` and
`Rh_*(D(p⁻¹)(F[0]))`. This verifies the actual map, not just its endpoints.
No second definition of this notion has been introduced.

Edge cases:

- Empty U, X, or Y are allowed: neither `Nonempty` nor a positive dimension is
  assumed. The maps, sheaf categories, degree-zero functor, and torsion predicate
  remain defined on empty schemes. If U or the product is empty, the resulting
  zero cases are included.
- The zero sheaf and identity open immersion are included. The predicate holds
  for zero stalk elements with n = 1; no nonzero condition is imposed on F.
- There is no integer coefficient or cohomological-degree binder in the theorem:
  no n = 0 case is lost by introducing one. Inside the existing torsion predicate
  n must be positive, just as in the node. n = 1 is allowed. The sheaf is in
  degree zero and the isomorphism is in the whole unbounded derived category.
- In characteristic zero, every positive n is nonzero in K; this is ordinary
  torsion. In characteristic p, nonzero `(n : K)` means prime-to-p torsion.
  Neither characteristic is excluded, and no uniform n has been introduced.
- `u` is explicitly bound and arbitrary. Schemes and fields use the existing
  `Scheme.{u}`/`Type u` size convention; coefficients use the recorded
  `AddCommGrpCat.{u+1}`. There is no extra universe equality or independent
  lower universe for geometric test fields. Small separably closed geometric
  points of `Type u` include separable/algebraic closures of residue fields of
  these schemes and form the recorded conservative family; larger geometric
  points give the same stalks by separably closed field extension. Thus this
  convention excludes no geometric point case of the node.

Mismatch and recovery log:

1. The retained sandbox was empty of delivery artifacts; reconstructed its node
   copy, module, and report. There was no earlier review section to overwrite.
2. Found the existing `openProductExchange` definition during independent source
   searches. Reused it and added its landed owner to the statement dependencies;
   did not introduce a private or duplicate exchange definition.
3. No mismatch was found between the mathematical source, DAG statement, final
   signature, or the used dependency definitions. The item statement, proof,
   proof dependencies, and all unit/target statements remain unchanged.
4. No new nodes or dependency modules require additional H12/H13 review. The only
   theorem has the whole proof `sorry`; no definition has postponed data.
5. Header, source/blueprint docstrings, all ten proof steps, line widths, explicit
   universe and variables, and verbatim `lean.statement` were checked by eye and
   by direct text comparison.

Validation: prescribed `scompile.py N9 lem-kun-0f1h` passed on the server.
The delivered library module compiled in 4.4 seconds, with no errors or warnings.
All required overlays compiled separately within the 60-second limit. Direct
text checks confirm the node signature is verbatim equal to the file, the only
node changes are `lean` and the added landed statement dependency, every Lean
line is at most 100 characters, and the sole postponed theorem has proof `sorry`.
`deliver2.py N9 lem-kun-0f1h --no-push` printed OK: commit
`57b3077a49` passes server preflight and compiles. Final delivery reruns both
gates with this validation note included.
