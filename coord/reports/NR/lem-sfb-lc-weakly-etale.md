## Worker report

Item: `lem-sfb-lc-weakly-etale`. Group: NR. Date (UTC): 2026-10-16.

This delivery attaches the exact existing declaration
`AlgebraicGeometry.ProEtale.weaklyEtale_toSpecZ_profiniteToScheme` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`. No module, definition,
or theorem is added. Only the item's `lean` field is changed. The module is
published in the `newtargets-dag` side framework described in
`coord/pefw-upstream-framework.md`; it is absent from the older slopmaster2
checkout. I read both the side copy and the current published source using
`scompile.py --source WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
The published source has the same signature and a proof where the older side
copy has `sorry`; this delivery does not modify either source or claim a proof
audit of its imports.

Exact recorded signature (the source's namespace is `AlgebraicGeometry.ProEtale`
and its explicitly declared universe is `u`):

```lean
instance weaklyEtale_toSpecZ_profiniteToScheme (S : Profinite.{u}) :
    WeaklyEtale (toSpecZ (profiniteToScheme.obj S))
```

Hypothesis and clause correspondence:

- “Let S be a profinite set” is exactly `(S : Profinite.{u})`, for arbitrary `u`.
  The bundled object supplies compactness, Hausdorffness, and total disconnectedness;
  it does not supply or require nonemptiness.
- “LC(S,Z), the ring of locally constant functions S to Z” is precisely
  `LocallyConstant S ℤ`. Reading the real data of `profiniteToCommRingCatOp`
  shows its object is `op (CommRingCat.of (LocallyConstant S ℤ))`. Mathlib's
  `LocallyConstant` bundles a function and its local constancy, and its ring
  instance has pointwise operations.
- “Spec LC(S,Z)” is `profiniteToScheme.obj S`: the actual definition is
  `profiniteToCommRingCatOp ⋙ Scheme.Spec`. Mathlib's spectrum functor at that
  object is exactly `Spec (.of (LocallyConstant S ℤ))`.
- “the morphism to Spec Z” is `toSpecZ (profiniteToScheme.obj S)`.
  `specZ : Scheme.{u}` is `Spec (.of (ULift.{u} ℤ))` and `toSpecZ X` is
  `specULiftZIsTerminal.from X`. ULift changes only the size representation of
  the integer ring. Uniqueness of maps to this terminal scheme identifies the
  arrow with spectrum of the constant-integer ring map (after that canonical
  coefficient lift). The current published proof explicitly uses this
  terminal uniqueness to identify its spectrum map with `toSpecZ`.
- “is weakly etale” is `AlgebraicGeometry.WeaklyEtale` applied to that exact
  arrow. The recorded Mathlib class has the two fields `flat : Flat f` and
  `flat_diagonal : Flat (pullback.diagonal f)`. Thus the conclusion includes
  flatness of the diagonal, not only flatness of the underlying algebra.

Dependency declarations read and used:

- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`, and `Spec.homEquiv` in
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`. I read their full signatures
  and docstrings. `Spec.map` is contravariant, with the required direction.
- `def-weil-scheme-morphism-properties` is explicitly a convention collecting
  pointers and has no declaration of its own. Its weakly-etale clause points
  to `def-weil-weakly-etale-morphism`, whose recorded Mathlib match is
  `AlgebraicGeometry.WeaklyEtale` in
  `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`. I read that node and the
  full class declaration, including both flatness fields. The existing
  module publicly imports this class and Mathlib's locally constant ring API.
- The existing module itself supplies `profiniteToCommRingCatOp`,
  `profiniteToScheme`, `specZ`, and `toSpecZ`; their definitions and docstrings
  were read in full. Mathlib's `specULiftZIsTerminal` in
  `Mathlib.AlgebraicGeometry.Limits` fixes the structure map.

Source and edge-case checks:

I read the current main-20261015 blueprint statement and proof, and all five
steps of the DAG proof. The finite nonempty clopen partitions form a nonempty
directed system, with the empty partition when S is empty. Every function has
finite image by compactness and occurs at a finite-product stage. Compatible
maps descend uniquely through a common refinement, giving the filtered
colimit of these integer algebras. Each finite product of integers is etale,
including the zero ring for an empty product. This is an ind-etale
presentation, so the ind-etale stability theorem gives weak etaleness of the
constant-integer map and hence of its spectrum. This is the full flat-diagonal
conclusion of the blueprint. The existing declaration asserts exactly that
conclusion; no additional proof-dependency imports are introduced because no
new module is written.

The empty profinite space is included: LC(empty,Z) is the zero ring and its
spectrum is empty. No `Nonempty`, `Nontrivial`, finite-presentation, or finite-S
hypothesis occurs. A singleton gives LC(S,Z) isomorphic to Z and its structure
map is an isomorphism. Finite S gives the expected finite product. Infinite S
is included without asserting that LC(S,Z) is finitely presented. The arbitrary
universe and the lifted base allow profinite sets of every size. There is no
statement correction, disputed statement, missing dependency, or new node.

Searches (performed for this item, with raw service results retained in the
sandbox's `searches.jsonl`):

- `msearch.py ... leansearch "Locally constant functions on a profinite space
  form a weakly etale algebra"`: eight hits, including `LocallyConstant`,
  `LocallyConstant.freeOfProfinite`, and finite-quotient factorization; none is
  this scheme statement.
- `msearch.py ... leanfinder "The spectrum of locally constant integer valued
  functions on a profinite space is weakly etale over the integers"`: eight
  hits on standard-etale algebras and etale loci/maps; no exact statement.
- `msearch.py ... loogle "LocallyConstant, Algebra.WeaklyEtale"`: zero hits.
- `msearch.py ... grep "weaklyEtale|weakly_etale"`: fifteen Mathlib hits,
  consisting of the ring/scheme weakly-etale definitions and pro-etale-site
  references; no locally constant scheme theorem.
- `rg` on slopmaster2 `WeilConjectures` for the exact declaration, the item id,
  and `profiniteToScheme`: no hit. Searching its source file inventory found
  supporting ring-theory modules, which do not replace the exact scheme item.
- `rg` on `lean/Sheaf` for `profiniteToScheme`, the exact declaration, and
  locally-constant/etale combinations: existing consumers include
  `ProfinitePointPullback` and `ProfiniteTestObjectFunctor`; neither supplies
  a separate exact declaration for this node.
- `rg` on the side `lean/WeilConjectures` finds the exact instance in
  `SixFunctors/ProEtale/ModuleObject/Basic.lean`, and the defining functors
  immediately above it. The blueprint's named Lean declaration is exactly
  this instance. `scompile.py --source` confirms the current published source.
- `rg` on `dag/lean_names_upstream.json` for the instance, functor, and
  `LocallyConstant.weaklyEtale`: no hit in that older source-name inventory.

Validation: the dedicated sandbox probe imports the existing module, checks
its fully explicit declaration, and prints its axioms through the prescribed
`scompile.py` wrapper. The delivery dry run also performs its own existing-name
compile and the maintainer's stage-2 preflight. The probe passed without warnings
in both its sandbox compile and its library check; `#check` of the existing
declaration passed. Because the attached declaration is an open stage-2
statement in the side framework, this delivery makes no proof-axiom claim
about it. The final dry run result is recorded below. No direct compiler,
global build, shared edit, or direct Git command is used.

Preflight repair: the first dry run required `lean.branch = "slopmaster2"`
for the `WeilConjectures` declaration namespace. That metadata is corrected;
the note retains the accurate published-overlay source provenance. Its only
other finding was the independent second reading, left to the second reader
as instructed. The final dry run follows this repair.

Final validation succeeded: `deliver2.py NR lem-sfb-lc-weakly-etale --no-push`
exited 0 and printed `OK (dry run): commit 5f64d1dab1 compiles and passes the
preflight except for the second reading, which the second reader writes;
nothing pushed.` The independent second-reading section is appended below. The delivery tool's
existing-declaration sandbox and library checks both passed. No delivery was pushed.


## Second reading by NR

I independently opened the node, its blueprint source, the existing declaration, and
both recorded statement dependencies. The node introduces exactly one object, a
profinite set `S`; its associated ring is `LC(S, ℤ)`, the ring of locally constant
functions `S → ℤ`; and its sole conclusion is that the induced morphism
`Spec LC(S, ℤ) → Spec ℤ` is weakly étale. The node has no base-field, characteristic,
Noetherian, finiteness, separatedness, or nonemptiness hypothesis.

The Lean rendering is the existing instance
`AlgebraicGeometry.ProEtale.weaklyEtale_toSpecZ_profiniteToScheme`
with signature

```lean
instance weaklyEtale_toSpecZ_profiniteToScheme (S : Profinite.{u}) :
    WeaklyEtale (toSpecZ (profiniteToScheme.obj S))
```

Here `(S : Profinite.{u})` is the arbitrary-universe bundled profinite set. The
recorded `profiniteToScheme` definition has object
`Spec (.of (LocallyConstant S ℤ))`, so it renders the node's `Spec LC(S, ℤ)` exactly.
The recorded `toSpecZ` is the unique structure map to `Spec (.of (ULift.{u} ℤ))`,
the canonical universe-lifted presentation of `Spec ℤ`; the lift changes the size
presentation of the coefficient ring only. `WeaklyEtale` is the recorded scheme
morphism property, including flatness of the map and of its diagonal. Thus every
object, quantifier, and conclusion clause agrees, with no stronger hypothesis or
weaker conclusion.

I checked the dependencies item by item. `def-weil-affine-spectrum` supplies
Mathlib's `AlgebraicGeometry.Spec` (and contravariant `Spec.map`); it does not
replace the bundled `profiniteToScheme` construction. The convention node
`def-weil-scheme-morphism-properties` points to
`def-weil-weakly-etale-morphism`, whose Mathlib notion is `WeaklyEtale` with the two
flatness fields. No dependency interface is unusable and no module or node repair is
needed.

The edge cases remain covered. `Profinite` does not require nonemptiness, so the
empty space is allowed (its locally constant-function ring is the zero ring and its
spectrum is empty); a singleton gives the expected integer spectrum; finite spaces
give finite products; and infinite profinite spaces are included without a finite
presentation assumption. The arbitrary universe `u` introduces no excluded case.

For the one-definition check I searched with alternate queries using LeanFinder
(`Spec LocallyConstant profinite WeaklyEtale`) and Loogle (the fully qualified
instance query), and searched Mathlib, the slopmaster2 source, `lean/Sheaf`, and the
side `lean/WeilConjectures` tree for `profinite.*weakly`,
`weakly.*profinite`, and `locallyConstant.*spec`. The only exact declaration is the
existing pro-étale instance recorded by the worker; the related general
`weaklyEtale_spec_map_algebraMap_locallyConstant` and the conjunction theorem
`profinite_point_pullback` do not have this item's exact statement. The searches
found no competing exact declaration in Mathlib or the older source tree.

The only report repair was factual: the worker report claimed that an axiom print
had no `sorryAx`, although the attached side-framework declaration is an open
stage-2 statement. I replaced that claim with the accurate type-check statement.
The Lean and node records are otherwise unchanged. There is no statement correction,
`STATEMENT-DISPUTED` flag, new node, or dependency module.
