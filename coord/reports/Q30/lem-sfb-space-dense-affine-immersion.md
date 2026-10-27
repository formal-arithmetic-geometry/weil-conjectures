## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseAffineImmersion` states
`AlgebraicGeometry.AlgebraicSpace.exists_dense_affineSpace_immersion`, with `sorry` as
its only proof. It introduces no definitions or auxiliary theorems. The node is changed
only in `lean`; its statement and dependency lists are unchanged.

Source read: `literature/stacks-project/spaces-limits.tex`, the complete statement and
proof of Tag 088N, `lemma-embedding-into-affine-over-qs`. The delivery specializes its
target to the specified affine Noetherian scheme, exactly as the accepted node does.
The declaration docstring carries all five steps of the accepted split, including the
finite disjoint affine union argument and the empty case.

Hypotheses and clauses, in the order of the node:

| Node text | Lean rendering |
| --- | --- |
| A scheme S and algebraic spaces over S, in the fixed universes | `{S : Scheme.{u}}`, the explicit `universe u`, and `(X : AlgebraicSpace S)` |
| A commutative Noetherian ring A | `(A : Type u) [CommRing A] [IsNoetherianRing A]` |
| B = Spec A with specified map to S | `(b : Spec (.of A) ⟶ S)` and `Over.mk b` |
| The morphism f : X to B | `(f : X ⟶ schemeSpace (Over.mk b))`; `schemeSpace` is the existing representable fppf sheaf of this actual S-scheme |
| Separated | `(hsep : MapIsSeparated f)` |
| Of finite type | `(hft : MapIsFiniteType f)`; this is the recorded conjunction of quasi-compactness and the locally-finite-type chart test |
| An open subspace U of X | `∃ (U : Over S) (j : yoneda.obj U ⟶ X.obj.obj), ... IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j` |
| Quasi-compact U | `CompactSpace U.left`, ordinary quasi-compactness of the representing scheme; no Hausdorff condition is imposed |
| Dense in the atlas point topology | `Dense (pointImage j)`, using the recorded point image and topology on `Point X.obj.obj` |
| An integer n at least zero | `(n : ℕ)`; zero is allowed |
| Relative affine n-space over B | `AffineSpace (ULift.{u} (Fin n)) (Spec (.of A))`; the universe lift changes neither the number of coordinates nor their ordering |
| An immersion a into that affine space | `(a : U.left ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of A)))` and `IsImmersion a` |
| The open subspace has the restricted map to B | `(g : U ⟶ Over.mk b)` and `j ≫ f.hom.hom = yoneda.map g` |
| The immersion is over B | `a ≫ (AffineSpace (ULift.{u} (Fin n)) (Spec (.of A)) ↘ Spec (.of A)) = g.left` |
| Immersion means closed followed by open on scheme tests | For the exhibited morphism between schemes, Mathlib `IsImmersion.isImmersion_iff_exists` is exactly the closed-then-open factorization; immersions are stable under scheme base change |
| In particular U is a scheme | U is explicitly an object of `Over S`, so its underlying object `U.left` is a scheme; its representable open immersion supplies the specified subspace |
| X and A need not be reduced, and X need not be irreducible or flat | There is no reducedness, irreducibility, flatness, domain, nontriviality or nonemptiness binder |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, and
  `AlgebraicGeometry.Spec` (`def-pc-scheme`, `def-weil-affine-spectrum`).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsRepresentableWith` (`def-trf-algebraic-space`). The latter tests every
  S-scheme and every map to the target and supplies an actual representing pullback.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsSeparated` and `AlgebraicSpace.MapIsFiniteType`
  (`def-sfb-space-morphism-properties`). Their definitions and chart-test signature were
  read in full; no private property of morphisms replaces them.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointImage` and `AlgebraicSpace.pointTopologicalSpace`
  (`def-a1-space-point-topology`). Its `PointRepresentative`, `Point` and `schemePointMap`
  prerequisites were also read in `AlgebraicSpacePointClasses`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`
  (`def-weil-pbc-noetherian-ring`). This is Noetherianity as a module over itself,
  equivalently finite generation of every ideal.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace` and its
  `AffineSpace.over` projection (`def-nagata-relative-affine-space`). Its index type is
  explicitly in `Type u`, as required by its full signature.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  (`def-weil-open-immersion`).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `AlgebraicGeometry.IsImmersion`, and `IsImmersion.isImmersion_iff_exists`
  (`def-weil-closed-immersion`, whose mathlib_match explicitly names the immersion API).
- `def-weil-size-convention` is a recorded metatheoretic convention: explicit universe
  parameters implement it, with no additional proposition or object to define.

The existing helper `AlgebraicSpace.schemeSpace` is imported from its defining module
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`. Its full definition and the supporting
`schemeSheaf_isAlgebraicSpace` signature/docstring were read: it takes the actual
representable fppf sheaf, with no arbitrary choice of algebraic-space model. This is
only the existing scheme-as-space realization of `def-trf-algebraic-space`, not a new
notion or a new hypothesis. No dependency interface repair is needed.

Proof imports include the recorded dense-scheme-open theorem, Mathlib Noetherian scheme
and topology facts, affine basis and coproduct-spectrum facts, the permanence and etale
facts, and the recorded `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineImmersion`.
The additional existing `WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart` exposes
`exists_isClosedImmersion_affineSpace_of_isAffine`, whose full statement and proof were
read: it is the affine-target polynomial presentation used in step 5. The recorded
main declaration of `lem-chow-affine-immersion` is the projective conclusion, so that
extra import makes the affine construction available without restating it. The proof
nodes `lem-sfb-space-quasiseparated-test-calculus` and
`lem-sfb-noetherian-space-topology` have no recorded declaration in this checkout;
their mathematical steps remain in the proof docstring and no proof is attempted.

Edge cases checked before drafting:

- Empty X: take the empty scheme as U; its image is dense in the empty point space,
  and it is quasi-compact and immerses into affine space. No nonempty witness is required.
- Zero ring A: Spec A and necessarily X are empty; the preceding case applies.
- n = 0: `ULift (Fin 0)` is empty and relative affine zero-space is the base; there is
  no positivity condition on n.
- Nonreduced examples, such as a finite-type dual-number scheme over a Noetherian base,
  are admitted with their original structure sheaves. No passage to a reduction occurs.
- Reducible X: the proof uses pairwise disjoint affine opens in component interiors,
  including intersecting components; neither the statement nor its types assumes a
  single component.
- The structural maps are retained in both triangles: the immersion cannot choose an
  unrelated B-structure. No restriction on the characteristic of A is imposed.
- Test schemes, A, S and coordinate index sets share the existing framework universe u;
  there is no independently smaller test universe that could make a hypothesis vacuous.

Searches for an existing statement (all performed before drafting):

- `msearch.py ... leanfinder "A separated finite type algebraic space over an affine
  Noetherian scheme has a dense quasi compact open subscheme immersing in finite
  dimensional affine space"`: 8 hits, concerning finite scheme morphisms, quasi-affine
  schemes, Noetherian schemes and quasi-compact scheme morphisms. None supplies the dense
  scheme open of an algebraic space.
- `msearch.py ... leansearch "A finite type algebraic space over an affine Noetherian
  scheme contains a dense quasi compact open subscheme with an immersion into affine
  space"`: 8 hits, including finite affine covers of quasi-compact scheme opens,
  quasi-affine schemes and the affine Zariski dense subsite. No exact match.
- `msearch.py ... loogle "AlgebraicGeometry.IsImmersion, AlgebraicGeometry.AffineSpace"`:
  successful query, zero hits.
- `msearch.py ... grep "dense.*(affine|immersion)|exists.*[Ii]mmersion|AlgebraicSpace"
  AlgebraicGeometry`: 5 hits, in `Sites/AffineEtale`, `Morphisms/Immersion` and
  `Morphisms/LocalIso`. They concern a dense subsite, immersion factorization or local
  isomorphisms, rather than the node's statement.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for dense affine/immersion statements
  and existence of immersions found the scheme polynomial embedding, projective Chow
  statements, and the already recorded algebraic-space dense-scheme-open theorem.
  None states this combination of finite type, quasi-compact dense open and relative
  affine immersion. A node-id search of `lean/WeilConjectures` returned no occurrence.
- Targeted searches in `AlgebraicSpace*.lean` and `Space*.lean` for dense affine opens
  returned no duplicate. Searching the chosen full declaration name in Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf` returned no match.

Validation: `scompile.py Q30 lem-sfb-space-dense-affine-immersion` compiled the delivered
file in both sandbox and library modes against the live published project, cleanly
(1.8 seconds and 1.5 seconds respectively). There are no new nodes, no dependency
modules, no statement correction and no disputed statement.

## Second reading by Q30

I reread the node and the completed module clause by clause as a self-check; the assigned
independent review is the maintainer's delivery review. The open immersion is explicitly
scheme-test representable, not merely an open set of point classes. Compactness is that
of U itself. Density is `Dense (pointImage j)` in the existing atlas topology. The result
asserts an immersion, although the proof plan produces a closed immersion; thus it does
not strengthen the conclusion by asserting U affine or a closed immersion. The separate
maps g and a, together with their two equations, ensure both describe the restriction
of the specified f over B. `n : ℕ` includes zero, and the universe lift only places the
finite coordinate type in the universe required by Mathlib. The only property binders
are exactly commutativity, Noetherianity, separatedness and finite type. I found no
mismatch and made no statement change. The only proof is `sorry`, all variables and
universes are explicitly bound, and all lines of the Lean file are at most 100 characters.
