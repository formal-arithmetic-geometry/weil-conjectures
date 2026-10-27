## Worker report

Stage 2, Q16, `lem-sfb-space-etale-maximum-degree`. The module
`Sheaf.AlgebraicGeometry.SpaceEtaleMaximumDegree` contains two statements with `sorry`:
`AlgebraicGeometry.AlgebraicSpace.affine_etale_atlas_finite_type_bounded` and
`AlgebraicGeometry.AlgebraicSpace.exists_affine_etale_atlas_maximum_degree`.
Together they render the entire node. No definition, construction data, axiom, or proof
is introduced. The node's mathematical statement and proof remain unchanged.

Sources read: `decent-spaces.tex`, lemma-bounded-fibres (03JX), especially the implication
from quasi-separatedness to universally bounded atlas fibres; lemma-quasi-compact-reasonable-
stratification (07S8), including its scheme-test proof; `spaces-cohomology.tex`,
lemma-weak-chow (089J), the first paragraph and the paragraph beginning the induction on d.
The latest blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`, (3), was also read;
this item is a supporting geometric prerequisite, not that unit's own statement.
No repair note exists for this item.

Hypothesis and clause correspondence:

- The absolute base is `Spec (.of (ULift.{u} ℤ))`. `universe u` is explicit; `ULift` is
  solely the canonical universe lift of Z. `A : Type u` with `[CommRing A]` is the given
  ring; `Over.mk (specULiftZIsTerminal.from (Spec (.of A)))` is precisely Spec A with
  its unique absolute structure map. `X : AlgebraicSpace ...` retains a general space,
  and `W : Over ...` retains the actual scheme atlas and its absolute structure map.
- `g` is the structure morphism X -> Spec A and `f : yoneda.obj W ⟶ X.obj.obj` is the
  given atlas. `hW : IsAffine W.left` says exactly that W is affine.
- `hsep : MapToSchemeIsSeparated X ... g` is the scheme-test closed-diagonal condition.
  `hqc : MapIsQuasiCompact g` and
  `hft : MapToSchemeIsLocally (@LocallyOfFiniteType) X ... g` are finite type:
  quasi-compactness and local finite type tested on etale source charts. The existing
  MapIsQuasiCompact is the project convention using affine scheme tests, equivalent
  here to the quasi-compact-open convention in the node. Finite presentation, universal
  closedness and properness in the node's introductory conventions impose no further
  hypotheses on X or its atlas; none are added.
- `he : IsEtale f` includes representability and etaleness on every scheme test;
  `hs : IsSurjective f` is scheme-test surjectivity. There is no additional finiteness,
  noetherian, characteristic, or finite-presentation assumption.
- In `affine_etale_atlas_finite_type_bounded`, the canonical W -> Spec A is
  `(yoneda.preimage (f ≫ g)).left`. `LocallyOfFiniteType` and `QuasiCompact` of that
  morphism are exactly its finite-type assertion.
- Its existential `b : ℕ` is the nonnegative integer bound. `PointRepresentative` binds
  every field, base map and field-valued section; `IsAlgClosed a.K` restricts to the
  geometric points. `yonedaEquiv.symm a.value` is that actual geometric-point map.
  `Point (Limits.pullback f (yonedaEquiv.symm a.value))` is the point set of the literal
  sheaf geometric fibre W times_X Spec(a.K). Its cardinal being at most b asserts both
  finiteness and the requested bound. Cardinal.mk, rather than Nat.card, prevents
  infinite fibres from being assigned cardinality zero.
- The same first theorem asserts `IsEmpty (Point X.obj.obj) → b = 0 ∧ IsEmpty W.left`:
  in the empty case the bound can actually be chosen zero and W is empty. The natural
  bound is available without a nonemptiness hypothesis.
- Only the second theorem assumes `hne : Nonempty (Point X.obj.obj)`. It returns d and
  `U : OpenSubspace X`, `1 ≤ d`, and `IsLeast` of the exact same set of geometric-fibre
  bounds. This is the least positive bound, not merely an attained or chosen bound.
- `(pointImage U.val.ι).Nonempty` asserts nonemptiness of the maximum open. The next
  equality identifies that image with precisely the point classes having an
  algebraically closed representative with fibre cardinal d. Point classes and their
  quotient relation are the existing definitions, not a set of chosen representatives.
  The following finite-etale test clause also ensures degree d for every geometric
  lift in this open. `OpenSubspace` encodes representable open immersions on tests.
- For every etale scheme test of U, expressed by `IsEtale (a ≫ U.val.ι)`, the witnesses
  E,p,q and `IsPullback q (yoneda.map p) f (a ≫ U.val.ι)` give its actual atlas pullback.
  `IsFinite p.left ∧ Etale p.left` says finite etale. The final conjunct is
  `((Scheme.Modules.pushforward p.left).obj (𝟙_ E.left.Modules)).IsFiniteLocallyFreeOfRank d`,
  precisely the direct-image structure algebra's underlying module locally free of
  constant finite rank d. No arbitrary algebra or unrelated comparison map is used.
- `C : ClosedSubspace X`, `IsReduced C.val`, and the image equality with
  `(pointImage U.val.ι)ᶜ` specify the reduced closed complement T. Its uniqueness is
  the already-recorded reduced-closed-support theorem. WT,p,q together with
  `IsPullback (yoneda.map p) q f C.val.arrow.hom.hom` identify WT with W times_X T;
  `IsAffine WT.left`, `IsEtale q`, `IsSurjective q`, and the final strict cardinal bound
  are exactly the four requested assertions about this base change.

Dependency interfaces used (full signatures and docstrings read in the source):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map`; the ring is `CommRingCat.of A` and affine schemes use `IsAffine`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `IsSurjective`, with actual presheaf maps on `Over S`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`;
  products in the statement are the corresponding literal presheaf pullbacks.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`,
  `pointTopologicalSpace`; `Point`, `PointRepresentative`, and `schemePointMap` are
  supplied by its PointClasses dependency. The size-convention node is metatheoretic;
  explicit u and the existing Point universe u+1 implement it.
- Scheme property modules `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `.FiniteType`, `.FinitePresentation`, `.Proper`, `.Etale`, `.Finite`, and
  `Mathlib.AlgebraicGeometry.OpenImmersion`: the existing `IsClosedImmersion`,
  `LocallyOfFiniteType`, `QuasiCompact`, `LocallyOfFinitePresentation`, `IsProper`,
  `IsSeparated`, `UniversallyClosed`, `Etale`, `IsFinite`, `IsOpenImmersion`.
  `Mathlib.Algebra.Field.Defs`: `Field` as the field notion.
- `Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport`:
  `exists_unique_reduced_closed_subspace`, with its existing `ClosedSubspace` and
  space `IsReduced` predicates. No reducedness is claimed for WT.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapToSchemeIsSeparated`,
  `MapToSchemeIsLocally`, `MapIsQuasiCompact`. The already-landed owning node
  `def-sfb-proper-curve-moduli` is added to stmt_deps, with no changes to that node.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`; its already-landed
  node `def-a1-space-open-subspace` is added to stmt_deps (it was already a proof_dep).
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`. Its already-recorded owning node
  `def-amb-finite-locally-free-module` is added to stmt_deps. The direct image is
  `Scheme.Modules.pushforward` and its input is the monoidal unit, the structure module.
  `def-weil-finite-integral-morphism` is also added for `IsFinite`. These four additions
  cite existing notions; no new node or dependency repair is necessary.

Proof imports include all the stated non-Mathlib proof modules: point-open calculus,
separable tensor splitting, representable etale scheme tests, etale fibre decomposition,
finite-flat pushforward, bounded scheme stratification and unramified quasi-finiteness.
The Mathlib affine, quasi-separated, closed-immersion and rank modules cover the leaf
proof dependencies. The currently unstated space closed-degree-loci, fibre-bound,
qcqs-permanence and separated-composition nodes have no module to import.

Edge cases checked against the signatures and sources: empty X and W (zero bound allowed);
zero ring A (its spectrum is empty); d=1 (T must then be empty by surjectivity); empty
scheme tests of U (finite etale and the rank assertion remain valid); nonreduced bases
(only T is required reduced); all characteristics; the disjoint union of the identity
sheet and a punctured-line sheet over A1 (maximum locus open, not a closed maximum
stratum); all field representatives in the site's universe. The point-space cardinal
is in universe u+1; no equality of unrelated universes or countability is assumed.

Searches actually run with msearch.py:

- LeanFinder: `An affine etale atlas of a separated finite type algebraic space has bounded
  geometric fibres and a nonempty finite etale maximum degree open`: 8 hits, including
  Scheme.Etale, IsEtale and ring etale-locus/standard-smooth results; no space statement.
- Loogle: `"Etale", "finite"`: 12 hits, including Algebra.Etale.finitePresentation,
  CommAlgCat.FiniteEtale and scheme etale instances; none states this atlas theorem.
- Mathlib grep: `AlgebraicSpace|maximum.degree|bounded.fibres`: 3 hits, all graph maximum
  degree declarations in Combinatorics/SimpleGraph/Finite.lean; no matching geometry.
- LeanSearch: `An affine etale atlas of a separated finite type algebraic space has bounded
  fibres and a finite etale open locus of maximum degree`: 8 hits, including ring etale
  loci, field product decompositions and the finite scheme fibre instance; no match.
- rg of WeilConjectures, Sheaf/AlgebraicGeometry, and dag/lean_names_upstream.json for the
  node id, both proposed names, maximum.degree and bounded.fibre: no node-id or declaration
  match; bounded fibre dimension and the scheme bounded stratification are different
  statements. AlgebraicSpaceDenseSchemeOpen mentions the maximum-degree argument in its
  proof but states existence of a dense scheme open, not this atlas result.
- Source searches for the existing space property, open-subspace, finite-map and
  finite-locally-free-rank declarations found the reusable interfaces listed above.

No statement dispute, source error or statement correction was found. The module
compiled cleanly through scompile.py after enabling the existing scoped monoidal-unit
notation; no additional theorem hypothesis or modified definition was needed.

## Second reading by Q16

The dispatcher prohibits starting another agent; this is the author's separate rereading,
with the node, Lean file, and Stacks 089J/07S8 open. Independent review belongs to the
maintainer. The first reading's only compile defect was the scope for `𝟙_`, repaired by
`open scoped MonoidalCategory`; it had no mathematical effect.

Checked each hypothesis against both signatures: arbitrary A, actual algebraic space X,
affine W, separatedness and finite type of X -> Spec A, and representable surjective
etaleness of the actual f. The first theorem has no nonemptiness assumption. The second
has exactly the nonempty-X condition of the node. No properness, noetherianity, extra
field hypothesis or fixed atlas trivialization enters either signature.

Reread every conclusion: the scheme map W -> B is recovered from f composed with g;
the geometric bound uses literal pullbacks and cardinals; the empty implication chooses
zero and forces W empty; IsLeast is on that same bound predicate; U is a nonempty open
subfunctor with precisely the maximum-degree point image; its finite-etale test squares
fix the actual maps and its rank assertion is for p_* O_E; C is reduced and closed with
exactly the complementary support; WT is the actual base change, affine and surjective
etale with a strict fibre bound. In particular the base change is not required reduced,
and d=1 and empty test schemes remain included. Existing point equivalence means that
using an algebraically closed representative describes the locus on |X| rather than a
locus of chosen lifts. No mismatch requiring a mathematical change was found.

The four stmt_deps additions only make the already-used, landed definitions explicit;
the old statement, proof and proof_deps are retained verbatim. No other node is edited.
