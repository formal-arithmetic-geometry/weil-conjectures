## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothMorphismCotangentIsomorphismEtale` states
`AlgebraicGeometry.smooth_morphism_cotangent_isomorphism_etale`, with proof `sorry`.
It introduces no definitions and makes no correction to the node statement. The only
additional statement dependency is the already landed definition node
`def-a1-relative-differentials-pullback-map`, whose canonical map is reused directly.

Hypothesis-by-hypothesis and clause-by-clause reading:

- Arbitrary schemes S, X, Y: `{S X Y : Scheme.{u}}`, with explicit universe `u`.
- Structure morphisms p and q: `(p : X ⟶ S) (q : Y ⟶ S)`.
- The specified morphism g: `(g : X ⟶ Y)`.
- The S-morphism equation qg=p: `(h : g ≫ q = p)`, using Lean's diagrammatic composition.
- Smoothness of both structure morphisms: `[Smooth p] [Smooth q]`.
- Every point x of X: `(x : X)` is an arbitrary explicit argument.
- Relative differential sheaves: `q.relativeDifferentials` and `p.relativeDifferentials`,
  supplied by the recorded upstream construction and its universal derivation.
- Module pullback: the domain of `q.relativeDifferentialsPullbackMap g` is exactly
  `(Scheme.Modules.tensorPullback g).obj q.relativeDifferentials`.
- The canonical O_X-linear map c_g: `q.relativeDifferentialsPullbackMap g` followed by
  `(Scheme.Hom.relativeDifferentialsCongr (g ≫ q) h).hom`. The first factor is the
  existing uniquely characterized universal-derivation map. Its generator formula
  sends `1 ⊗ db` to `d(g.app W b)`; O_X-linearity gives `a ⊗ db ↦ a d(g.app W b)`.
  The second factor only identifies equal structure morphisms, so its codomain is
  exactly `p.relativeDifferentials`, rather than a different sheaf or arbitrary map.
- Étale on an open neighbourhood of x:
  `∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ g)`. The restriction keeps codomain Y,
  which is equivalent to the usual source-and-target-open formulation.
- Induced map on stalks: `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).map`
  applied to that very canonical composite.
- Isomorphism of O_{X,x}-modules: `IsIso` in `ModuleCat (X.presheaf.stalk x)`.
- Both directions: the conclusion is `↔`, in the same order as the prose.
- No field, Noetherian, separatedness or relative-rank condition is imposed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
  The local pinned sources use these names; search-service `IsSmooth`/`IsEtale`
  hits use old names and were checked against the actual source.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`,
  `relativeDifferentialsHomEquiv`, and `relativeDifferentialsCongr`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  recorded dependency module for `def-pc-module-pullback`, exposing the upstream
  `Scheme.Modules.tensorPullback`; its section-normalized adjunction was read.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor` and its O_{X,x}-linear map implementation.
- `Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap`:
  `Scheme.Hom.relativeDifferentialsPullbackMap`, its explicit generator and
  `existsUnique_relativeDifferentialsPullbackMap`. The source gives the genuine
  canonical construction, determined by the section formula, not an arbitrary choice.

The proof dependency `lem-sfb-smooth-cotangent-etale-criterion` has no Lean record,
Mathlib match or closed upstream audit in the read DAG. Its entire pointwise statement
and proof relationship were read; no proof-only import can yet be supplied. The module
preserves the node's proof verbatim in mathematical content in its theorem docstring:
apply that criterion with h=g, identify dh=c_g by their generator formulas, and do not
use its additional equal-rank determinant clause. That criterion is needed for the
future proof, not to type this statement; no new prerequisite notion is missing.

Sources: read the local Stacks `morphisms.tex` lemma-etale-at-point (Tag 02GU),
including the flatness-and-zero-differentials and square-Jacobian conditions. Opened
BLR's primary scan at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf,
printed p.41, Corollary 10, PDF page 48 (zero-based page 47). Read the
actual Corollary 10 and Proposition 8 in the PDF text: the former gives the precise
pointwise equivalence, under smoothness at x and g(x). The node uses globally smooth
structure maps, as stated. The web screenshot endpoint returned a cache miss. Latest-blueprint search for this item's id and the
more general criterion had no hits, consistent with the node's non-blueprint origin.

Edge cases checked mathematically before writing:

- Empty X: there is no x, so the pointwise assertion is vacuous, without adding
  Nonempty or nonempty-neighbourhood hypotheses.
- g=id and p=q: c_g is the identity under the canonical identifications, and
  the entire source is an étale neighbourhood.
- Both structure morphisms étale: both differential sheaves vanish and an
  S-morphism between étale S-schemes is étale; rank zero is included.
- Frobenius on A¹ over F_p: its differential is zero on a nonzero rank-one stalk,
  and the map is not étale. No characteristic restriction was inadvertently added.
- A point mapping to A¹ over a field: the relative ranks differ, c_g is not an
  isomorphism, and the morphism is not étale. No equal-rank condition is assumed.
- Arbitrary nonreduced or non-Noetherian base: neither the canonical map nor the
  statement requires reducedness, Noetherianity, separatedness or dimension bounds.
- Disconnected sources with varying smooth relative dimensions are allowed;
  the assertion tests each stalk without a global dimension parameter.

Searches (all before writing the statement):

1. `msearch.py ... leanfinder` query: "A morphism between smooth schemes over a base
   is etale near a point if and only if its relative cotangent map on stalks is an
   isomorphism". Eight hits: IsEtale, its smooth/unramified instances, algebra étale
   locus and standard-smooth dimension-zero constructors; no matching theorem.
2. `msearch.py ... loogle` query: `"IsEtale", "relativeDifferentials"`.
   Successful search, zero hits.
3. `msearch.py ... grep` query:
   `etale.*(cotangent|differential)|[Ee]tale.*(Cotangent|Differential)|(cotangent|differential).*etale`
   in `AlgebraicGeometry`. Successful search, zero hits.
4. `msearch.py ... leansearch` query: "A morphism between smooth schemes over a base
   is etale precisely where its differential is an isomorphism". Eight hits concern
   étale/smooth definitions, ring étaleness and formal étaleness; none matches.
5. `rg` of project `lean/WeilConjectures` and `lean/Sheaf` for cotangent/differential
   and étale combinations, then focused source reads: found and reused
   `RelativeDifferentialsPullbackMap`; `EtaleAtPointFromDifferentials` assumes a field,
   finite type, quasi-compactness and a prescribed affine coordinate map, so it is
   not this arbitrary-base equivalence. Coordinate-lift lemmas are also different.
6. Item-id search in `lean/WeilConjectures`: no existing implementation. Full proposed
   declaration-name search of Mathlib, WeilConjectures, Sheaf and
   `dag/lean_names_upstream.json`: no collision. Read every recorded statement
   dependency and declaration signature/docstring, including the added canonical map.

Server compilation through the prescribed `scompile.py` succeeded for both sandbox
and final module (1.7 s and 1.6 s), with no errors or unexpected warnings.
There is no STATEMENT-DISPUTED issue, no statement correction, no new node and no
replacement dependency module.

## Second reading by Q05

This is the worker's own second pass, not a claim of independent review; the brief
assigns independent review to the maintainer. Reopened the node and final module and
checked all correspondences listed above. In particular the equation has the correct
orientation for diagrammatic composition, the canonical map's codomain is transported
to p's actual differential sheaf, the stalk is an O_{X,x}-module stalk, and the left
side asserts étaleness of the restriction of the specified g. No stronger geometric
hypothesis, residue-field tensoring, free-rank condition, or arbitrary differential map
has replaced the node's data. No mismatch or further change was found.
