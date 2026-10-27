## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceLftSmoothFpqcLocality` states this node in two
named theorems, both with `sorry`. It defines no notion and changes no mathematical
statement. The only node changes are its Lean record and the addition of four already
landed statement dependencies whose canonical declarations the signature uses.

The sources read were `spaces-descent.tex`, definition-local-source-target (06F8),
remark-list-local-source-target (06FC), item (3), and
lemma-descending-property-locally-finite-type (041S), including the proof. The first
specifies exactly three conditions; the remark includes locally finite type; 041S
supplies fpqc locality. The node's seven proof steps are reproduced in the two
proof docstrings, split as steps 1--3 and 4--7. No proofs are supplied.

Hypotheses and clauses, matched to Lean:

* The base scheme is `{S : Scheme.{u}}`; all spaces are `AlgebraicSpace S` and all
  arrows are morphisms in that category. No Noetherian, separated, quasi-compact,
  nonempty, or representability hypothesis is imposed.
* Local finite type on compatible etale scheme charts is exactly
  `MapIsLocally (@LocallyOfFiniteType)`. Smoothness is exactly
  `MapIsLocally (@Smooth)`. `MapIsLocally` quantifies over every pair of representable
  etale scheme charts and every commuting scheme arrow, using the existing scheme
  predicate. Thus neither property is replaced by a property of arbitrary maps or
  by representability by schemes.
* Clause (i) is the first conjunct of
  `locallyOfFiniteType_smooth_local_source_target`: a smooth `a : X ⟶ Y` and a
  locally finite type `f : Y ⟶ Z` give local finite type of `a ≫ f`.
* Clause (ii) is its second conjunct: for locally finite type `f : X ⟶ Y` and smooth
  `b : V ⟶ Y`, `enlargedFibreProductFst b f` is locally finite type. This is the
  first projection `V ×_Y X → V`, hence the stated base-changed morphism.
* Clause (iii) is its final conjunct, an equivalence for every `r : X ⟶ Y`.
  `∀ x : Point X.obj.obj` is every field-valued point class. The existential binders
  give precisely `U, V, a, b, h, p`; the conjuncts assert that `a, b` are smooth,
  `mapPoint a.hom.hom p = x`, `a ≫ r = h ≫ b`, and `h` locally finite type.
  Neither chart is required to be surjective. The point `p` is a point class of U,
  not a chosen rational point of a smaller field.
* The final fpqc and fppf assertions are together
  `locallyOfFiniteType_iff_of_schemeTestCover`. `J` ranges over scheme precoverages;
  `hJ` restricts it to exactly `Scheme.fpqcPrecoverage` or `Scheme.fppfPrecoverage`.
  Thus these are two instances of one statement, with no unnamed topology assumed.
  `I : Type w`, `Yᵢ`, and `g` are arbitrary covering families over the space Y.
* The node's convention on scheme pullbacks is expanded as `hcover`. For every
  `T : Over S` and every `t : yoneda.obj T ⟶ Y.obj.obj`, it tests arbitrary
  surjective representable etale scheme atlases
  `a i : yoneda.obj (U i) ⟶ pullback (g i).hom.hom t`.
  The required scheme family has arrows
  `(yoneda.preimage (a i ≫ pullback.snd (g i).hom.hom t)).left` and its presieve
  must belong to `J T.left`. This is the canonical composite from each atlas to T.
  There is no assumption that the space pullbacks themselves are schemes. This
  is the scheme-chart meaning of the node's scheme-pullback convention: etale
  atlases are fppf and fpqc covers, and covering membership is unchanged by
  surjective etale refinement. Arbitrary atlases, rather than a supplied special
  atlas, keep the covering condition intrinsic.
* The conclusion is an `↔`, with the right hand side quantifying over every i and
  applying the same local finite type predicate to
  `enlargedFibreProductFst (g i) r : Yᵢ ×_Y X → Yᵢ`. Swapping the fibre-product
  factors identifies this with the node's `X ×_Y Yᵢ → Yᵢ`.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsSurjective`, including their complete representable scheme-test signatures.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
* `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `fpqcPrecoverage`, `fppfPrecoverage`
  (the family notions, rather than only their generated Grothendieck topologies).
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`.
* `Mathlib.Algebra.Field.Defs`: `Field`, through the point-class construction.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `Point`.
* `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `mapPoint`.
* `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `enlargedFibreProductFst` and
  `enlargedFibreProduct`, the actual sheaf pullback bundled using
  `fibreProduct_isAlgebraicSpace`. These plain definitions are owned by the existing definition node
  `def-sfb-space-sheaf-fibre-product`, recorded with `existing: true` in this exact
  module. Their data are `Limits.pullback` and `pullback.fst`; the algebraic-space
  property is a proposition supplied by `fibreProduct_isAlgebraicSpace`. They are
  not choices extracted from the enlarged ringed-site theorem.

The four added `stmt_deps` are `def-sfb-space-morphism-properties`,
`def-a1-algebraic-space-point-classes`, `def-sfb-proper-curve-moduli`, and
`def-sfb-space-sheaf-fibre-product`. These already have landed Lean
records; no dependency repair or new node is needed. Other original statement
modules are publicly available through the two space framework imports and the
explicit Mathlib imports.

The module imports the recorded modules of every stated proof dependency, directly
or through a statement dependency. In particular the fibre-product theorem is a public
import of EnlargedEtaleRingedSite, and scheme open immersions being etale is in
Mathlib.Morphisms.Etale. The currently unstated proof dependencies
`lem-sfb-space-fppf-source-locality-transfer` and
`lem-sfb-space-fpqc-property-affine-criterion` have no modules to import; they remain
named in the proof docstrings and are not needed to type the statement. Their
statements are not replaced or assumed as additional hypotheses.

Edge cases checked before writing and again against the completed signature:

* Empty X: the pointwise condition is vacuous, and local finite type has its usual
  empty-source meaning. The proof docstring explicitly uses the empty source cover.
* Empty index: `I : Type w` has no Nonempty instance. The scheme-test cover condition
  then requires the empty presieve to cover every scheme mapping to Y, forcing Y
  empty by field tests; local finite type and the empty universal right side agree.
* Empty members are permitted in covers and in all etale atlases. Identity smooth
  maps give the forward pointwise witnesses without a surjectivity hypothesis.
* Non-scheme spaces and nonrepresentable covering arrows are included, since all
  scheme tests are performed after taking the actual presheaf pullback and an atlas.
* Test schemes and fields have the same u as the site; no independently smaller
  testing universe makes the hypotheses vacuous. Point classes live in u+1 as the
  recorded definition requires. The family index has unrestricted universe w.
* No characteristic, dimension, finiteness of I, or affine/separated intersection
  condition appears. No quasi-compactness was silently added to local finite type.

Searches actually run:

1. `msearch.py ... leanfinder` with query "Locally finite type morphisms of algebraic
   spaces are smooth local on source and target and fpqc local on target": eight
   scheme-level hits, including composition of LocallyOfFiniteType and local finite
   presentation of smooth maps; no algebraic-space statement matching this node.
2. `msearch.py ... loogle` with query
   `AlgebraicGeometry.LocallyOfFiniteType, AlgebraicGeometry.Smooth`: one hit,
   `smooth_of_grpObj`; no match for this locality statement.
3. `msearch.py ... grep` with query
   `AlgebraicSpace|fpqc.*locallyOfFiniteType|locallyOfFiniteType.*fpqc` in
   AlgebraicGeometry: zero Mathlib hits.
4. `rg` in `lean/WeilConjectures/AlgebraicGeometry` for the node id, AlgebraicSpace,
   smooth_local and fpqc_local: only unrelated smooth-local depth-two results.
5. `rg` in `lean/Sheaf/AlgebraicGeometry` for covering and smooth/local-finite-type
   notions found the existing MapIsLocally interface, the flat/proper/fp locality
   sibling (which does not state this theorem), and IsFppfCover (which is not a
   scheme-precoverage test for both topologies). No copied definition was introduced.
6. `rg` over `lean/Sheaf`, `lean/WeilConjectures` and `dag/lean_names_upstream.json`
   for the item id and the two proposed theorem names returned no collisions.

No STATEMENT-DISPUTED issue and no source correction. The source explicitly includes
local finite type in 06FC(3) and fpqc locality in 041S. Compiled by the prescribed
`scompile.py` in both sandbox and library module mode: clean, 4.5 s and 3.6 s.

## Second reading by NU

A separate rereading pass by this worker opened the node and completed module and
checked the displayed binders and conclusions, as detailed above. The dispatcher
prohibits starting another agent; this section does not claim an independent worker
review. The maintainer performs the independent delivery review.

The pass checked the orientation of composition (`a ≫ r = h ≫ b`), the target of the
base-change projection (`enlargedFibreProductFst b f` goes to V), the point class
binder (`Point U.obj.obj`), and the exact predicates on both smooth vertical maps.
It also checked that the covering condition quantifies over schemes mapping to an
arbitrary space Y, not just a scheme target, and that the target-test map is recovered
from the pullback's canonical projection by Yoneda. The two choices of J give both
requested covering topologies. No extra representability or nonemptiness constraint
was found. No theorem signature changed in the rereading; the report was expanded to
explain the scheme-atlas interpretation and the reason for each added landed dependency.

## Repair of returned head 29a1e66baf23

H2: replaced the added statement dependency
`lem-trf-space-enlarged-etale-ringed-site-model` with its existing definition owner
`def-sfb-space-sheaf-fibre-product`, landed on 2026-10-23. Read its full statement,
Lean record and both definitions in `EnlargedEtaleRingedSite.lean`: the definitions
supply the actual sheaf pullback and first projection used in both theorem signatures.
Updated the dependency paragraph accordingly. Compared the retained node with the
current read-only base: only `lean` and `stmt_deps` differ; no other field is changed.
The Lean module remains byte-for-byte the returned module, as the return requests.
The optional import-trimming advisory is left unchanged: the existing plain imports
retain the recorded stage-3 proof plan, following the stage-2 import convention.

Repair rereading checked that all four added dependencies now name landed definition
owners, that the removed theorem is absent from `stmt_deps`, and that
`EnlargedEtaleRingedSite` remains the public import providing both constructions.
The mathematical clause correspondence and empty/universe cases remain exactly those
accepted by the independent immutable-head review.
