## Worker report

The target is already on `newtargets-dag` from NF's earlier stage-2 delivery of this
node (repair of f646f851403d).  Q88 changed no Lean and no statement; the module
`Sheaf.CategoryTheory.Sites.OrientedProductSliceLocalization` is the landed one, byte
for byte, including its author line (group NF).  The `lean` record keeps NF's note,
prefixed by a sentence recording this unchanged re-record.

Rendering of the node statement (ILO XI 1.10(b), (1.b)–(1.c)):

- $f:X\to S$, $g:Y\to S$ morphisms of schemes: `(X S Y : Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S)`.
- $P=X_{\mathrm{Et}}\overleftarrow\times_{S_{\mathrm{Et}}}Y_{\mathrm{Et}}$ on the triple site:
  `Sheaf (orientedEtaleTopology f g) (Type (u + 1))` (landed in
  `Sheaf.Paper.OrientedAffineNeighbourhoodLimit`, built on `OrientedProduct.largeTopology`
  of lem-trf-oriented-product-universal).
- Triple $Z=(U\to V\leftarrow W)$: `(U : X.Etale) (V : S.Etale) (W : Y.Etale)
  (a : U ⟶ f.Etale.obj V) (b : W ⟶ g.Etale.obj V)`, packaged as
  `⟨(U, W), V, (a, b)⟩ : OrientedEtaleTriples f g`.  The maps $U\to V$, $W\to V$ are
  `orientedTripleLeft Z`, `orientedTripleRight Z`; they are not assumed etale.
- $H_Z=h_Z^\#$: `(orientedEtaleAssociated f g).obj Z` (sheafified `uliftYoneda`, no
  subcanonicity assumed).
- $U_{\mathrm{Et}}\overleftarrow\times_{V_{\mathrm{Et}}}W_{\mathrm{Et}}$:
  `Sheaf (orientedEtaleTopology (orientedTripleLeft Z) (orientedTripleRight Z)) (Type (u + 1))`.
- Localization morphism induced by $U\to X$, $V\to S$, $W\to Y$: `t`, whose direct image
  is restriction along `orientedSliceBaseChange Z` (`Comma.map` of the three base-change
  functors `Z.left.1.hom.Etale`, `Z.right.hom.Etale`, `Z.left.2.hom.Etale` with the
  canonical `pullbackComp` comparisons `orientedSliceLeftBaseChangeIso`,
  `orientedSliceRightBaseChangeIso`); real data, no choice.
- Equivalence $P/H_Z\simeq Q$ over $P$ with the slice projection identified with `t`:
  `∃ e : Over H_Z ≌ Q, Nonempty (Over.star H_Z ⋙ e.functor ≅ t.inverse)`.

Edge cases: arbitrary schemes (empty ones included), no affineness, separatedness or
subcanonicity; $U\to V$, $W\to V$ arbitrary; single universe `u` for schemes, sheaf values
in `Type (u + 1)` as for the landed etale triple site; no universe equality imposed.

Compile: `tools/nt_compile.py --json` on the module, clean (3.1 s), only the theorem's
`sorry`.  Searches (DAG, Mathlib, slopmaster2): no other declaration states this; the
recorded declaration is the canonical one.  No dry run output is reproduced here.

## Second reading by Q88

No second reading by a worker: since 2026-10-17 the worker delivers directly and the
maintainer's independent review is the only review.  The maintainer's reviewer restored
NF's author line and `lean.note` (the delivery had replaced them although nothing was
changed) and replaced this report with the clause-by-clause rendering above.
