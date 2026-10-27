## Worker report

The new module `Sheaf.AlgebraicGeometry.SpaceLimitOpenCoverDescent` states
`AlgebraicGeometry.AlgebraicSpace.exists_stage_finite_qc_open_cover` with one postponed
proof. No definitions, helper axioms or extra theorem obligations are introduced.
The node changes in `lean` and by adding the landed definition node
`def-sfb-space-absolute-quasi-separated` to `stmt_deps`. Its accepted split,
statement and source are preserved.

Statement correspondence:

- The base is `{S : Scheme.{u}}`; algebraic spaces and their fppf sheaves are the
  existing `AlgebraicSpace S`. No separatedness or finiteness condition on S is imposed.
- The index is `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`,
  in the scheme universe, and `D : Iᵒᵖ ⥤ AlgebraicSpace S` is the inverse system.
  A preorder is sufficient and admits every directed partially ordered set.
- `hqc` gives a surjective representable etale atlas from a quasi-compact scheme for
  every stage, literally the node's definition of quasi-compactness.
- `hqs` uses `IsAbsolutelyQuasiSeparated` at every stage. Its affine-test definition
  is the existing equivalent formulation of quasi-compactness of the absolute
  diagonal, rather than a condition on the structure map to a possibly non-qsep S.
- `haff` states representability with scheme property `IsAffineHom` for every
  transition. This is the node's affine condition on every affine scheme test:
  representability with affine projections on all scheme tests is the usual equivalent
  formulation. It does not assert that a scheme source has to be affine over a
  nonaffine test target.
- `X`, `π`, and `hlim` specify the algebraic-space limit and its actual projections.
  The limit cone is in fppf sheaves (`D ⋙ ObjectProperty.ι IsAlgebraicSpace`), so
  the hypothesis is the sheaf limit in the node, with no arbitrary comparison map.
- `i₀ : I` is the prescribed lower bound. `{A : Type u} [Finite A]` represents the
  finite family, including the empty family. `W : A → OpenSubspace X` uses the
  recorded subfunctors representable by open immersions, with no new open notion.
- `hWqc` gives exactly the quasi-compact scheme atlases of the given opens.
- `hcover` is `(⋃ a, pointImage (W a).val.ι) = Set.univ`. Point images use the
  recorded field-valued classes and atlas topology. Sectionwise supremum of open
  subfunctors is deliberately not used: a map into a union need not factor globally
  into one member of an open covering.
- `∃ i, i₀ ≤ i ∧ ∃ V` gives the eventual index and descended opens.
  `(V a).val.preimage (π.app (op i)).hom = (W a).val` states their canonical
  inverse-image equality as subfunctors on every scheme test, not an abstract
  isomorphism which might forget the inclusion.
- The later-stage clause quantifies over *every* `j` with `i ≤ j`, including `j = i`.
  Its `Vj` is tied by equality to the actual `Subfunctor.preimage` of V. It asserts
  quasi-compactness by a qc etale atlas, absolute quasi-separatedness by the expanded
  affine-test formula of `IsAbsolutelyQuasiSeparated`, and full union of point images.
  At `j = i`, functoriality identifies the transition with the identity, so equality
  of subfunctors identifies Vj with V. Thus this clause states all three properties
  of V itself, as well as all later inverse images. No quasi-separatedness of a mere
  topological point space is substituted for the algebraic-space condition.
- The final clause treats all `i ≤ j ≤ k` and each family member. The source and
  target of q are the literal inverse images of V at k and j. Its displayed equation
  says the square with their open inclusions commutes. Because those inclusions are
  monomorphisms, this equation determines q uniquely, namely the canonical restricted
  transition. `IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) q` states that
  this very map is affine. Existence here introduces no arbitrary choice of map.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, `IsSurjective`.
  The existing sheaf, diagonal and atlas definition is used without replacement;
  the small etale structure sheaf is supplied by this framework but is not an argument
  of this purely open-subspace statement.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `Point`, `pointImage`,
  `pointTopologicalSpace` (also imported through the existing absolute-qsep module).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`, the existing definition for the node's inline
  absolute-diagonal condition. For unbundled open presheaves its formula is written
  explicitly, since the existing definition takes a bundled algebraic space.
- `def-weil-size-convention` is a metatheoretic convention, as its recorded `lean`
  says. Explicit universe u on schemes, inverse indices and finite indices implements it.
- `Mathlib.CategoryTheory.Subfunctor.Image`: `Subfunctor.preimage`, the literal
  canonical inverse-image construction (available through `OpenSubspace`).

The available proof-dependency modules are imported non-publicly: the scheme
limit-affine-transition module; algebraic-space fibre products, etale image opens,
chartwise etale permanence and point/open calculus; and Mathlib's affine-transition
limit module. The remaining unstated proof dependencies have no module to import.
Mathlib leaves are present transitively through these modules (affine scheme qcqs,
affine permanence, open immersions etale, and scheme open descent).

Sources read: `spaces-limits.tex`, Situation `situation-descent` (084R),
`lemma-descend-opens` (0827), `lemma-limit-nonempty` (086W); the accepted node's
six-step proof and finite-cover argument for 07SR. This agrees with the source's
qcqs and affine-transition hypotheses. No correction or dispute is needed.

Edge cases checked before writing and again on the final signature: A empty forces
X to have no points and the conclusion forces an eventual empty stage; empty members
are permitted; repeated opens are permitted; a singleton family W = X is permitted;
a constant system descends at the prescribed stage; empty stages and empty base are
permitted; no transition is assumed surjective; non-quasi-separated base schemes are
not excluded. The formula for covers avoids the false sectionwise-union assertion.

Searches run (all wrapper searches are logged in `searches.jsonl`):

- leanfinder: "finite quasi-compact open cover descends along an inverse limit of
  quasi-compact quasi-separated algebraic spaces with affine transitions": eight
  scheme results, including `Scheme.exists_isOpenCover_and_isAffine` and
  `exists_preimage_eq`; none is the algebraic-space statement.
- leansearch: "finite quasi-compact open cover descends along inverse limits of
  algebraic spaces with affine transition maps": eight results, again scheme-cover
  and affine-transition-limit theorems; no algebraic-space result.
- loogle: "Subfunctor.preimage, CategoryTheory.Limits.IsLimit": unknown identifier
  `Subfunctor.preimage`, zero hits from that service; local Mathlib inspection finds
  the fully qualified `CategoryTheory.Subfunctor.preimage` in Subfunctor/Image.lean.
- wrapper grep: `descend.*[Oo]pen|[Oo]pen.*[Cc]over.*[Ll]imit`, AlgebraicGeometry:
  13 hits, scheme results and unrelated descent.
- rg on both `lean/WeilConjectures` and `lean/Sheaf` for the same expression and
  for the node id: scheme descent and spectral-space descent exist, but no theorem
  of this algebraic-space statement. Name collision search for
  `exists_stage_finite_qc_open_cover` in Mathlib and both library roots found none.
- rg for OpenSubspace, affine, quasi-compactness and quasi-separatedness found the
  existing interfaces listed above; these are reused rather than duplicated.

Validation: `scompile.py N7 lem-sfb-space-limit-open-cover-descent` compiled both
its sandbox view and its actual library module, in 1.8 s and 1.7 s respectively,
with no errors or warnings. The sole proof remains `by sorry` as stage 2 requires.

## Second reading by N7

A separate pass in this worker compared the finished signature with every clause
of the node. No independent worker review is claimed: the dispatch brief prohibits
starting agents, and the maintainer's independent delivery review follows.

The pass checked especially that `hlim` is a limit of fppf sheaves, that hqs is
absolute over Spec Z rather than relative over S, that the finite index may be empty,
that preimage equality preserves the specified projections, and that the j = i case
of the later-stage clause includes qcqs and covering of V itself. It also checked
that q is uniquely constrained by the monic open inclusion, so it cannot be an
unrelated affine map. No missing hypothesis or clause and no signature changes were
found. The repair adds the missing landed definition to `stmt_deps`; no new or
dependency modules are needed.

## Repair of return on 131b9718343e

1. H2/H4: added `def-sfb-space-absolute-quasi-separated` to the item's
   `stmt_deps`, as requested under STMT_DEPS MAY GAIN LANDED NODES. Its landed
   record names `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated`
   in `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`, which the
   theorem already imports publicly and uses in `hqs`. Re-read that definition's
   full affine-test formula and docstring. The Lean module and verbatim signature
   stay exactly as reviewed; the inline formula for unbundled open subspaces is
   retained, since there is no OpenSubspace-to-AlgebraicSpace bundling.

Compared the retained returned packet with the current main node: only `lean`
differed before this repair. Refreshed the node from current main, retained the
delivered Lean record, and appended only the requested statement dependency. The
delivery wrapper rebuilds the packet on current main. This is a dependency repair,
with no change to the mathematical statement and no `statement_change` required.

Second reading of the repair: the newly cited node is exactly the owning node of
the hqs declaration. All original statement dependencies remain present. The
Lean file is unchanged, so every clause checked in the maintainer's return remains
as reviewed. Compile and delivery preflight are rerun below through the prescribed
wrappers.
