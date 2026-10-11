## Worker report

The module `Sheaf.RingTheory.RegularLocalExtVanishing` states
`IsRegularLocalRing.subsingleton_ext_of_ringKrullDim_lt`, with proof `sorry`.
There are no new definitions, new nodes, dependency modules, or statement corrections.

Hypotheses and conclusion, clause by clause:

- The commutative ring is `(R : Type u) [CommRing R]`.
- The regular local ring `(R, m)` is `[IsRegularLocalRing R]`. This Mathlib class
  includes `IsLocalRing R` and `IsNoetherianRing R`, and equates the number of
  generators of its maximal ideal to `ringKrullDim R`. The maximal ideal is
  canonical, so it need not be supplied as separate data.
- `d = dim R` is used directly as `ringKrullDim R`, rather than introducing an
  extra variable and equality hypothesis. Its value has type `WithBot ℕ∞`.
- Every finitely generated module `M` is `(M : ModuleCat.{v} R)` with
  `[Module.Finite R M]`; every module `N` is `(N : ModuleCat.{v} R)` with no
  finiteness hypothesis.
- The degree and inequality are `(q : ℕ)` and
  `(hq : ringKrullDim R < (q : WithBot ℕ∞))`. Although the prose calls q an
  integer, q > dim R implies q > 0: a local ring is nontrivial, its dimension
  is nonnegative, and regular local dimension is finite. Thus natural degrees
  represent precisely all integer degrees covered by the node, with no cases
  lost; Mathlib's recorded `def-pc-ext` declaration takes natural degrees.
- `Ext^q_R(M,N) = 0` is `Subsingleton (Abelian.Ext M N q)`. Mathlib's Ext is
  an abelian group type, not a group object to compare to a zero object. Since
  it contains zero, subsingleton means every Ext element is zero, exactly the
  stated vanishing.
- `letI := HasExt.standard (ModuleCat.{v} R)` supplies the universally existing
  Ext construction. It is not a hypothesis. It works without assuming
  `Small R` or enough projectives in a restricted universe. Ring universe `u`
  and module universe `v` are independent and explicitly bound. Any pair of
  modules can be placed in a common universe; neither finite modules nor
  arbitrary coefficient modules are restricted to the universe of R.

Dependency declarations inspected and used:

- `def-weil-regular-scheme`: its Mathlib match `IsRegularLocalRing`, from
  `Mathlib.RingTheory.RegularLocalRing.Defs`, full class and docstring read.
  The ring component is exactly what this item needs; the scheme component
  of that definition node is unused here.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`, from
  `Mathlib.RingTheory.KrullDimension.Basic`, definition and docstring read.
  It is available through the regular-local import.
- `def-pc-ext`: `CategoryTheory.Abelian.Ext`, from
  `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`, definition, group
  structure, and `Ext.homAddEquiv` signature/docstring inspected. It uses
  shifted Hom between single complexes in the quasi-isomorphism localization,
  as the node requires. `HasExt.standard` from the same module supplies its
  size instance. `Mathlib.Algebra.Category.ModuleCat.Abelian` supplies the
  abelian module category instance.

Edge cases: d=0 yields vanishing exactly for q≥1, as for a field. For d=1
it yields vanishing for q≥2, as for a DVR. At q=d the strict inequality is
false, so the statement makes no erroneous claim about top-degree Ext.
At q=0 the inequality cannot hold for a regular local ring. The zero ring
is excluded by the local-ring hypothesis, as in the source. Zero M or N
is allowed and has trivial Ext. No restriction is imposed on characteristic.
Infinite N is allowed. No mathematical fault or disputed statement was found.

Source checked: the local Stacks files are absent on this machine, so the
published passages were opened at https://stacks.math.columbia.edu/tag/0FZ3
and https://stacks.math.columbia.edu/tag/00O7. The former's proof of (1)
uses local dimension d_x to deduce local Ext vanishing for q>d_x; the latter
supplies global dimension at most d. The theorem docstring records the node's
complete two-step proof using `lem-weil-pbc-regular-local-finite-gl-dim` and
`lem-weil-pbc-projective-dimension-ext-characterization`, with their tags.

Searches for an existing statement:

- `msearch.py leansearch`, query `regular local ring Ext vanishes above Krull
  dimension`: service unavailable (Internal Server Error), recorded without
  a verdict.
- `msearch.py leanfinder`, query `Ext groups over a regular local ring vanish
  above its Krull dimension`: eight hits, all abstract projective/injective
  dimension Ext-vanishing characterizations; no regular-local bound.
- `msearch.py loogle`, query `IsRegularLocalRing, CategoryTheory.Abelian.Ext,
  ringKrullDim`: zero hits.
- `msearch.py grep`, query `Ext.*regular|regular.*Ext`, Mathlib/RingTheory:
  twelve hits, principally regular sequence and depth/Rees statements;
  none is this theorem.
- `rg` on `WeilConjectures` and `lean/Sheaf`, query
  `ext.*[Rr]egular|[Rr]egular.*ext|lem-sc-regular-local-ext-vanishing`:
  only unrelated regular geometry, extensions, and regular-hom extensionality;
  no existing theorem for this node. The item-id search gave no upstream hit.
- `rg` on `dag/lean_names_upstream.json`, Mathlib, WeilConjectures, and
  `lean/Sheaf`, query `subsingleton_ext_of_ringKrullDim_lt`: no hit, confirming
  the full declaration name is fresh.

Validation: the module compiles on the server with no errors or warnings.
The required delivery dry run is run after this report and node record are written.

## Second reading by E1

I independently opened the item JSON, its source passages, all three statement
dependency records and their actual Mathlib declarations, and the delivered Lean.
There are no new nodes, dependency modules, or statement_change to review.

Object/hypothesis/conclusion checklist (H3):

- Commutative ring R: `(R : Type u) [CommRing R]`. Exact.
- Regular local (R,m): `[IsRegularLocalRing R]`. Exact: the class in
  Mathlib.RingTheory.RegularLocalRing.Defs extends IsLocalRing and
  IsNoetherianRing and asserts maximal-ideal spanFinrank = ringKrullDim.
  The canonical maximal ideal renders m, with no additional choice or hypothesis.
  This is the ring component of def-weil-regular-scheme's recorded match;
  the scheme component is not needed for this ring statement.
- d = dim R: `ringKrullDim R`, from the recorded
  Mathlib.RingTheory.KrullDimension.Basic declaration, is the supremum of
  prime-chain lengths. Substitution for d is exact, not a dimension assumption.
- Every finitely generated M: `(M : ModuleCat.{v} R) [Module.Finite R M]`.
  Exact; Module.Finite is finite generation, not finite cardinality.
- Every module N: `(N : ModuleCat.{v} R)`, without a finiteness instance. Exact.
- Every integer q>d: `(q : ℕ)` and
  `(hq : ringKrullDim R < (q : WithBot ℕ∞))`. Exact reindexing: local rings
  are nontrivial (IsLocalRing extends Nontrivial), so d≥0, and every integer
  above d is a positive natural number. No negative case is lost.
- Ext^q_R(M,N)=0: `Subsingleton (Abelian.Ext M N q)`. Exact, since Ext
  has an AddCommGroup instance and therefore contains zero. Ext.Basic defines
  it using localized shifted Hom of the single complexes; its homAddEquiv
  identifies it with the derived-category Hom of def-pc-ext. ModuleCat.Abelian
  supplies the abelian category at independently bound ring/module universes.
- `letI := HasExt.standard (ModuleCat.{v} R)` supplies a proved, universally
  available size instance, not an additional hypothesis. No Small R assumption.
  Quantification of M,N,q,hq covers the node's order of universal quantifiers.

Source review: local Stacks .tex files are absent, so I opened the authoritative
published passages [0FZ3](https://stacks.math.columbia.edu/tag/0FZ3),
[00O7](https://stacks.math.columbia.edu/tag/00O7), and
[065R](https://stacks.math.columbia.edu/tag/065R). The local algebra extracted
from the scheme argument requires only regular locality. The global scheme
hypotheses of 0FZ3 are not hypotheses of this extracted ring lemma. 00O7 gives
projective dimension at most d, and 065R gives vanishing for every coefficient
module above that bound. The delivered docstring carries those two node proof
steps in order, with their node ids and sources. It retains the finite M
hypothesis of the item, even though the global-dimension bound is stronger.

Edge cases: d=0 permits precisely q≥1; d=1 permits q≥2; q=d is excluded,
and q=0 has impossible hq. Zero M and zero N are admitted. The zero ring is
excluded by the source's local-ring convention and Lean's Nontrivial superclass.
There is no characteristic restriction and infinite N is admitted. Empty index
sets and empty schemes are not objects of this statement. Universes u and v
are explicitly bound and independent; any two modules can be lifted to one
common universe, so their shared v does not omit a mathematical case.

Independent duplicate searches (H4), using queries distinct from the worker's:

- msearch.py leanfinder: `finite module over regular local ring has vanishing
  higher extension groups` returned eight abstract projective/injective
  dimension vanishing lemmas, none with the regular-local Krull bound.
- msearch.py loogle: `IsRegularLocalRing, Subsingleton` returned zero hits.
- msearch.py leansearch: `regular local module projective dimension bounded
  by ring dimension` was unavailable (Internal Server Error); no verdict.
- rg on Mathlib/RingTheory/RegularLocalRing, WeilConjectures, and lean/Sheaf:
  `global.?dim|projective.?dim|subsingleton.*ext|ext.*subsingleton`.
  I followed the upstream hit IsRegularLocalRing.exists_hasProjectiveDimensionLE
  in WeilConjectures.Mathlib.RingTheory.Regular.ProjectiveDimension (line 199).
  It states only existence of some finite projective-dimension bound, not
  the Krull-dimension bound and not this Ext statement. It is not a match.
  The landed GlobalDimension module defines global/projective dimension;
  it does not state the item. Other hits concern unrelated sheaf Ext.
- rg for the item id and `subsingleton_ext_of_ringKrullDim_lt` in the upstream
  name table, WeilConjectures, and lean/Sheaf found no existing declaration.

Verdict: no statement mismatch, duplicate notion, hollow definition, or extra
proved theorem. The single theorem proof is sorry, its source/proof docstring
is complete, every binder is explicit, and conventions and imports are correct.
I left the Lean and node signature unchanged and added this independent review.
The upstream search above supplements the first report's narrower searches.
