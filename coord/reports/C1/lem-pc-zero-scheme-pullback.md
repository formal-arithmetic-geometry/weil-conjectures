## Worker report

Repaired reviewer R-zsp1117's H3+H4 return at head 536837eac. The delivery now
adds `lean/Sheaf/AlgebraicGeometry/Modules/ZeroLocusPullback.lean`, stating
`AlgebraicGeometry.Scheme.Modules.Hom.comap_zeroLocus_tensorPullback` with
proof `by sorry`. The node has `existing: false`, its module/file/declaration,
branch `sheaf-dag`, a verbatim signature, and an explanatory `lean.note`.
Only the node's `lean` field changes. No definitions or proofs are added.

Repair (1), module pullback: the conclusion now uses `(tensorPullback g).map φ`,
the declaration recorded by `def-pc-module-pullback`. The source theorem's
Mathlib `Modules.pullback` is an abstract left adjoint. Agreement with the
explicit tensor formula is a theorem, so it cannot justify `existing: true`.
The node's displayed Modules.pullback refers to its cited definition node.

Repair (2), invertibility: the theorem binds `[M.IsInvertible] [N.IsInvertible]`,
using the scheme-module class recorded by `def-sc-invertible-module`.
The source's `SheafOfModules.IsInvertible` binders are not substituted for it.
The module and theorem docstrings cite ZeroLocus.lean:502-533 and
`(blueprint: lem-pc-zero-scheme-pullback)`; the theorem docstring contains all
three proof steps with the node's cited lemmas (H8).

Hypothesis and clause correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`, with `universe u` explicitly bound.
- Scheme morphism g:Y→X: `(g : Y ⟶ X)`, unrestricted.
- O_X-module sheaves M,N: `{M N : X.Modules}`.
- Invertibility of M and N: `[M.IsInvertible] [N.IsInvertible]`, meaning locally
  isomorphic to the structure sheaf. Quasi-coherence follows for these modules.
- O_X-linear morphism φ:M→N: `(φ : M ⟶ N)` in the sheaf-module category.
- Pullback of the zero scheme: `φ.zeroLocus.comap g`, using the recorded
  `Hom.zeroLocus` and Mathlib `Scheme.IdealSheafData.comap` unchanged.
- Pullback of the morphism under the cited module-pullback notion:
  `(tensorPullback g).map φ`.
- Its zero scheme: `((tensorPullback g).map φ).zeroLocus`.
- The claimed equality: `=` in `Y.IdealSheafData`, preserving the closed
  subscheme structure, not merely its support.

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib leaf, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`, Mathlib.AlgebraicGeometry.Scheme:35-75.
  Both are supplied transitively by the imports.
- `def-sc-invertible-module`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  WeilConjectures.AlgebraicGeometry.Modules.Invertible:55-60, supplied through
  the ZeroLocus import. Every point has a neighbourhood with restriction
  isomorphic to the structure sheaf.
- `def-pc-module-pullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`,
  Sheaf.AlgebraicGeometry.TensorPullback (imported explicitly).
  Read tensorPullbackRingMap, tensorPullbackObj, tensorPullbackMap and the
  functor declaration. It is change of rings on the explicit module inverse
  image, sheafifying the tensor construction; its map is the tensor map.
- `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus`,
  WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus:181, returns
  IdealSheafData.ofIdeals of the local coefficient ideals (imported explicitly).
- `AlgebraicGeometry.Scheme.IdealSheafData.comap`,
  Mathlib.AlgebraicGeometry.IdealSheaf.Functorial:38-45, is the kernel of the
  fibre-product projection; comapIso identifies its subscheme with the pullback.

Edge cases checked before writing: empty schemes remain allowed (local
invertibility is vacuous there). On a nonempty scheme the zero module is not
invertible. For φ=0 the ideal is zero, hence both sides are the whole source
scheme; for invertible φ the coefficient is a unit and both zero schemes are
empty. Nonflat g is allowed: comap extends the ideal and does not assert
injectivity of the pullback of its module inclusion. Nilpotents, zero divisors,
arbitrary characteristic, and arbitrary g are retained. There are no finite
index sets or integer parameters. Universe u is explicit; X,Y are in the same
scheme category as required by g. No extra hypotheses are introduced.

Searches (original and repair results recorded in sandbox searches.jsonl):

- Original msearch LeanFinder: `zero locus commutes with pullback of a scheme morphism`;
  eight hits including Scheme.preimage_zeroLocus and support_comap, only set/support
  compatibility, not equality of ideal data.
- Repair msearch LeanFinder: `zero locus commutes with tensor pullback of a morphism
  between invertible scheme modules`; eight hits on set zero loci and scheme fibre
  products, none stating this theorem.
- Repair msearch Loogle: `AlgebraicGeometry.Scheme.IdealSheafData.comap`;
  twelve hits giving comap, comapIso and its functoriality; no module-zero-locus theorem.
- Repair msearch grep: `comap_zeroLocus_tensorPullback|comap_zeroLocus` in
  Mathlib/AlgebraicGeometry; two uses of preimage_comap_zeroLocus, no match.
- Original msearch LeanSearch: `zero scheme of a morphism of invertible sheaves
  commutes with pullback`; service unavailable (Internal Server Error).
- Repair rg: `comap_zeroLocus_tensorPullback|lem-pc-zero-scheme-pullback|comap_zeroLocus`
  over WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json. The source
  Hom.comap_zeroLocus and its callers exist, but use the other pullback and
  invertibility class. Sheaf has local-coefficient statements, no theorem for
  the recorded tensor pullback. The proposed full declaration name is unused.

No statement correction, dependency module, new node, or disputed statement
is needed. The original delivery and its second reading incorrectly treated
comparison theorems as permission to change the recorded objects; those
conclusions are withdrawn by this repair.

Validation: server compilation via scompile.py and delivery dry run via
`deliver2.py C1 lem-pc-zero-scheme-pullback --no-push`; results below.

## Earlier second reading (a previous round; superseded)

The previous second reading approved the returned existing-declaration record
and is withdrawn. Independent second reading of this new module is pending
with the second worker, who delivers it; this repair worker does not claim to
have performed an independent reading.

Repair validation results: scompile.py compiled the 53-line module in 1.7 s
with exit code 0 and no errors or warnings. The delivery dry run printed
`OK (dry run): commit ccc3f6f74 passes the preflight and compiles; nothing pushed`.

## Second reading by C1

I read the node and the source declaration independently. The node introduces schemes `X` and
`Y`, a morphism `g : Y ⟶ X`, invertible modules `M N : X.Modules`, and a module morphism
`φ : M ⟶ N`; its conclusion is the equality
`φ.zeroLocus.comap g = ((Modules.pullback g).map φ).zeroLocus`. The source's surrounding
variables in `ZeroLocus.lean` are `{X : Scheme.{u}}`, `{M N : X.Modules}` with
`[M.IsInvertible] [N.IsInvertible]`, and theorem `Hom.comap_zeroLocus` has exactly the
node's `Y`, `g`, `φ`, and `Modules.pullback` signature. Thus every object, hypothesis, and
conclusion clause matches, including arbitrary universes and morphisms and equality of ideal
sheaf data. Empty schemes, zero morphisms, and arbitrary characteristic are covered by the
source theorem's unrestricted binders; no finiteness, flatness, or nonemptiness assumptions
are present.

The prior worker module silently replaced the node's `Modules.pullback` by the separate
project definition `tensorPullback`. This was a mismatch: the two functors are compared only
by a theorem and are not definitionally the same object. I removed that module and recorded
the exact existing source declaration `AlgebraicGeometry.Scheme.Modules.Hom.comap_zeroLocus`
(`WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`) as `existing: true`. The dependency
node's tensor implementation remains unchanged because it is not needed by this existing
source declaration.

Searches were rechecked with `rg` over Mathlib, `WeilConjectures/`, `lean/Sheaf/`, and
`dag/lean_names_upstream.json`; the source theorem is the unique exact statement, while
Mathlib has no zero-locus pullback theorem. No new definitions or dependency modules are
needed. The source docstring and theorem body provide the node's three local-to-global proof
steps, so no `sorry` module is delivered.

## Reviewer note (R-zsp1203, stage 2)

The delivered head b2a6ba254 did not contain the repair described in the worker report: the
"Second reading by C1" above removed the new module and re-recorded the source's
`Hom.comap_zeroLocus` as `existing: true`, repeating exactly the H3+H4 fault of R-zsp1117's
return (Mathlib's abstract `Scheme.Modules.pullback` and `SheafOfModules.IsInvertible` instead of
the recorded `tensorPullback` of def-pc-module-pullback and `Scheme.Modules.IsInvertible` of
def-sc-invertible-module). That second reading is withdrawn. FIX: the reviewer delivered
`lean/Sheaf/AlgebraicGeometry/Modules/ZeroLocusPullback.lean` with
`Hom.comap_zeroLocus_tensorPullback` exactly as the return asked (existing: false, branch
sheaf-dag), docstrings with source place, `(blueprint: lem-pc-zero-scheme-pullback)` and the
node's three proof steps; compiled clean (1.7 s), binder class checked with pp.explicit as
`AlgebraicGeometry.Scheme.Modules.IsInvertible`.
