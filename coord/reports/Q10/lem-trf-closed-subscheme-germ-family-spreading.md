## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedSubschemeGermFamilySpreading` states
`AlgebraicGeometry.closedSubscheme_germ_family_spreading`, with its sole proof
`sorry`. It introduces no definitions and changes only the item's `lean` field.
The complete six-step accepted proof is rendered in the theorem docstring.

The previous stale-assignment ending concerned stage 1. I read the current
brief-stage2 section 0, the live node and queue: the item is stage 2 in
coord/queue.tsv, its split has passed review, and it has no Lean record. No
released repair note names it. Thus this delivery preserves the accepted split
and supplies its Lean statement, as the stage handoff explicitly requires.

Hypothesis and clause correspondence:

- A locally Noetherian scheme and a point: `{Y : Scheme.{u}}`,
  `[IsLocallyNoetherian Y]`, and `(y : Y)`.
- Any finite set F: `{F : Type v} [Finite F]`. The universe v is independent
  of the scheme universe u. Neither a nonempty family nor a chosen enumeration
  is imposed. A finite subset of an ambient set is equivalently its subtype;
  the statement quantifies over the whole finite index type.
- Two closed subschemes for every a: `Z H : F → Scheme.{u}`,
  `i : ∀ a, Z a ⟶ Y`, `j : ∀ a, H a ⟶ Y`, and the two pointwise
  `IsClosedImmersion` instances. The defining ideals are exactly `(i a).ker`
  and `(j a).ker`, with no additional independent ideal choices.
- Equality of embedded ideal stalks: `hgerm` equates the linear-map ranges
  of the stalk maps of `(i a).ker.toModulesι.val` and
  `(j a).ker.toModulesι.val`. Both ranges lie in the very same stalk of the
  structure module. Its canonical identification with the ring stalk preserves
  equality, so this is precisely equality as embedded ideals, rather than an
  abstract isomorphism of ideal modules. The recorded presheaf-module stalk
  functor applies to the underlying presheaves of these sheaves.
- One affine open neighbourhood: `∃ U : Y.affineOpens, y ∈ U.1 ∧ ...`.
  All subsequent clauses lie inside this one existential.
- Equality of each pair of pulled-back closed subschemes: an isomorphism
  `pullback (i a) U.1.ι ≅ pullback (j a) U.1.ι` commuting with their second
  projections to U. Equality of embedded closed subschemes is precisely this
  unique isomorphism over U, as the node's proof step 4 specifies.
- Every subset S: `∀ S : Finset F`. Since F is finite this includes every
  subset, including the empty subset, without an ordering restriction.
- Scheme-theoretic intersection: the existing Mathlib closed subscheme
  `(⨆ a ∈ S, (i a).ker).subscheme` is used. Suprema of ideal sheaves are sums,
  by `IdealSheafData.ideal_iSup`; this is the literal definition in Stacks
  Tag 0C4H, definition-scheme-theoretic-intersection-union. Its inclusion is
  `.subschemeι`. No new notion or private intersection construction is needed.
- Pullback of the Z intersection equals the intersection of the restricted H
  factors: the first S-conjunct gives an isomorphism from the former pullback
  to `(⨆ a ∈ S, (pullback.snd (j a) U.1.ι).ker).subscheme`, commuting with
  their maps to U. The latter kernel ideals are exactly the defining ideals
  of H_a ×_Y U, so this is an equality of embedded intersections.
- For U = Spec B the intersection ideal is the sum of the J_a: the second
  S-conjunct evaluates the kernel ideal of the Z intersection pullback at the
  top affine open of U and equates it to the indexed supremum of the kernel
  ideals of the H pullbacks at the same top open. Here B is canonically
  Γ(U, top), and U has its canonical affine-spectrum identification; this
  avoids adding a choice of ring or presentation. In a commutative ring,
  the ideal supremum is the ideal sum. Thus the displayed supremum is exactly
  the node's sum, also for empty S.
- Empty S: `S = ∅ → IsIso (...) ∧ ... = ⊥` states that the inclusion of
  the intersection into U is an isomorphism and its ideal is zero.
- An empty H factor with index in S: `∃ a ∈ S, IsEmpty (pullback ...)`
  implies `IsEmpty` of the Z intersection pullback and that its ideal is `⊤`.
  The previously asserted isomorphism transports these to the H intersection.

Dependency declarations read and used:

- pqf-def-locnoeth: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (all affine section rings Noetherian).
- def-weil-closed-immersion:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding, surjective stalk maps).
- def-weil-pbc-module-stalk:
  `WeilConjectures.Topology.PresheafModuleStalkFunctor`,
  `PresheafOfModules.moduleStalkFunctor`, with its full signature and germ-map
  construction read. It is used directly, not replaced by a second functor.
- def-pc-fibre-product:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, and its universal property;
  scheme pullbacks come from `Mathlib.AlgebraicGeometry.Pullbacks`.
- def-weil-affine-spectrum: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map`; the affine-open representation and
  `isAffineOpen_top` are Mathlib's canonical presentation of U = Spec B.
- def-sbc-closed-immersion-ideal-sheaf:
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`, `AlgebraicGeometry.Scheme.Hom.ker`,
  `.ker_apply`, and `Scheme.IdealSheafData`. The module bridge
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` supplies
  `.toModules` and `.toModulesι`. All are the existing notions.

All recorded proof dependencies are imported, either through public statement
imports or through the plain proof imports: Noetherian.Defs, Modules.Tilde,
ResidueField (including affine basic-open and stalk localization APIs),
Localization.Ideal, MonoidLocalization.Away, GammaSpecAdjunction, and
Morphisms.ClosedImmersion (including equal-kernel lifts).

Sources read locally: coherent.tex lemma-local-isomorphism (01Y3),
morphisms.tex definition-scheme-theoretic-intersection-union (0C4H) and the
following fibre-product lemma, plus the full accepted node and its proof.
The 0C4H definition explains directly why the existing ideal-sum subscheme
is the intersection used in the statement; no additional definition node is
required. The module docstring explains this representation.

Edge cases checked before finalizing the statement:

- Empty F: no stalk hypotheses; an affine neighbourhood of y still exists.
  S can only be empty, and the asserted intersection is U with zero ideal.
- Empty S with nonempty F: indexed supremum is bottom, the whole ambient
  scheme. IsIso of the inclusion expresses equality with U over U.
- Empty H factor: its defining ideal is top, hence so is the sum; the
  intersection is empty. There is no nonemptiness assumption on any factor.
- Y empty: there is no y, exactly as in the node, so the theorem has no
  instance to check. Nothing silently excludes an allowed point.
- Equal zero ideals (whole-scheme factors) and unit ideals (empty factors)
  satisfy the intended interpretations; nilpotents are retained by kernels.
- In Spec k[x], V(x) and V(x(x-1)) have equal ideal stalks at (x), and agree
  after inverting x-1. They need not agree globally, so U is existential and
  unrestricted. No reducedness, separatedness, domain, or global Noetherian
  assumption was introduced.

Searches made for an exact existing statement:

- msearch.py leanfinder: "Finitely many closed subschemes with equal ideal
  stalks at one point of a locally Noetherian scheme agree on a common affine
  neighbourhood and all their intersections have sum ideals". Eight hits,
  including ideal_ext_iff, IdealSheafData.ext_of_iSup_eq_top, subschemeCover,
  glueDataObj, ideal_iInf and ext_of_isAffine. None spreads equality at one
  stalk for a finite family or states all the intersection clauses.
- msearch.py loogle: `"IdealSheafData", "stalk"`: zero hits.
- msearch.py leansearch: "A finite family of pairs of closed subschemes with
  equal defining ideal stalks at a point agree on one affine open neighbourhood".
  Eight hits, led by IsAffineOpen.ideal_ext_iff and IdealSheafData extensionality.
  Those test equality on all stalks or on a cover, not a single-point spread.
- msearch.py grep: `IdealSheafData.*stalk|stalk.*IdealSheafData|exists.*ideal.*eq`
  in AlgebraicGeometry: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for ideal/stalk/germ-family
  combinations located the existing module bridge, closed-immersion stalk
  range theorem, and ideal-support material, but no exact statement.
- rg for the exact node id in both Lean roots: no hits. rg for the proposed
  declaration in both roots and dag/lean_names_upstream.json: no hits.
- Mathlib IdealSheaf Basic/Subscheme searches found the existing supremum,
  ideal_iSup, subscheme, subschemeι, kernel and empty/bottom APIs used here.
  The full dependency signatures and docstrings were opened before use.

Validation: scompile.py compiled the delivered file in both sandbox and library
module modes, each in 1.5 seconds, with no errors or warnings. The initial
elaboration probes were repaired by passing the explicit affine-open witness
and Scheme category for `IsEmpty` pullbacks. No diagnostic declarations remain.
There is no statement correction, dependency repair, or disputed statement.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
