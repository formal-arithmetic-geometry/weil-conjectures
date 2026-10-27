## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceImmersionAffineTests` states this node with
three named theorems, all with `sorry` proofs. No definition, auxiliary node,
dependency repair, or statement correction is needed. The node changes in `lean` and gains the existing joint-surjectivity definition
in `stmt_deps`, as requested in the return.
The three declarations are in namespace `AlgebraicGeometry.AlgebraicSpace`:
`immersion_iff_affine_scheme_tests`, `immersion_iff_exists_open_subspace_cover`, and
`immersion_presheafMap_baseChange`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. The size convention is rendered by explicit
  universe `u`; schemes, sheaves, scheme tests, and coefficient fields of the recorded
  joint-surjectivity predicate all use the existing algebraic-space framework at `u`.
- Arbitrary algebraic spaces over that base and their natural-transformation morphism
  are `(X Y : AlgebraicSpace S) (f : X ⟶ Y)`. None of the equivalence statements has a
  representability hypothesis.
- The condition “f is an immersion” is
  `IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left) f.hom.hom`.
  The recorded interface quantifies over every `T : Over S` and every map
  `yoneda.obj T ⟶ Y.obj.obj`, providing a representing scheme `U`, a scheme projection
  `p : U ⟶ T`, and a representing pullback square. Thus representability is part of
  this condition. Scheme `IsImmersion p.left` is exactly closed immersion followed by
  open immersion, as stated by Mathlib's `IsImmersion.isImmersion_iff_exists`.
- “Every affine scheme V → Y has scheme pullback immersed in V” is the right side of
  `immersion_iff_affine_scheme_tests`: `∀ (V : Over S), IsAffine V.left →` and every
  `a : yoneda.obj V ⟶ Y.obj.obj` admit `U : Over S`, `p : U ⟶ V`, and
  `q : yoneda.obj U ⟶ X.obj.obj` with
  `IsPullback q (yoneda.map p) f.hom.hom a ∧ IsImmersion p.left`.
  This states existence of the representing scheme, not just a property conditional
  on representability. A pullback square represents exactly the indicated sheaf fibre
  product, independently of a choice of representing object.
- “There exists an open-subspace covering of Y” is
  `∃ (I : Type (u + 1)) (U : I → OpenSubspace Y),
  IsJointlySurjective (fun i : I ↦ (U i).val.ι) ∧ ...`.
  `OpenSubspace` is the dependency's recorded subtype of subfunctors with inclusions
  representable by open immersions. Joint surjectivity is the existing condition on
  field-valued point representatives, precisely the point-covering convention of the
  fibre-product dependency. The index universe admits all families of open subspaces
  in the chosen bound, without assuming a finite or nonempty cover.
- “Each restriction is an immersion” is
  `∀ i : I, IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
  (Limits.pullback.snd f.hom.hom (U i).val.ι)`.
  The projection is the canonical presheaf fibre product over Y; its source is the
  underlying presheaf of the sheaf fibre product. The recorded open-subspace notion
  already ensures these are algebraic-space restrictions. The second theorem's `↔`
  supplies equivalence with the first condition; together the two equivalences give
  equivalence of all three conditions in the node.
- “Preserved by arbitrary algebraic-space base change” is
  `immersion_presheafMap_baseChange`, with arbitrary `(Y' : AlgebraicSpace S)` and
  `(g : Y' ⟶ Y)`, only the immersion hypothesis `hf` on f, and the conclusion
  `IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
  (Limits.pullback.snd f.hom.hom g.hom.hom)`.
  There is no restriction on g, and the projection is to Y', as required.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`. The latter has the full
  scheme-test signature, with a representing `IsPullback` square and scheme property.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`; their signatures/docstrings give the sheaf pullback,
  its universal property, and the joint-surjectivity convention.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity` (explicit public import):
  `AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective`, owned by the existing node
  `def-trf-algebraic-space-jointly-surjective-family`, now included in `stmt_deps`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion` and
  `IsImmersion.isImmersion_iff_exists`. The immersion import exposes these scheme
  notions and their characterization, without redefining them.
- `def-weil-size-convention` is a metatheoretic convention, not a Lean object or import.

Proof-plan imports include the recorded scheme representability theorem
`AlgebraicGeometry.isRepresentable_of_isSheaf_of_zariskiCovers` from
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability` as a plain import.
The other recorded proof dependencies are already exposed by the statement imports:
`Scheme.zariskiPrecoverage_le_fppfPrecoverage`,
`isOpenImmersion_stableUnderBaseChange`, and
`IsZariskiLocalAtTarget.of_range_subset_iSup` specialized to scheme `IsImmersion`.
Each theorem's docstring records its portion of the accepted four-step node proof.

Source checked directly: `literature/stacks-project/spaces-morphisms.tex`,
`lemma-closed-immersion-local` (Tag 03M4), especially immersion cases (1), (3), (5), and
`literature/stacks-project/spaces.tex`, `definition-immersion` (02YU) and
`lemma-base-change-immersions` (02YW). These impose no representability assumption
before the tests. The local source confirms the unchanged node statement.

Edge cases checked before writing: empty source and target schemes/spaces; the empty
index family (only covering a space without points); a one-member identity open cover;
identity and arbitrary nonrepresentable base-change morphisms; arbitrary affine tests
including the empty affine scheme; infinite open covers. No nonempty, quasi-compact,
separatedness, or finiteness assumptions occur. Scheme tests have the same universe as
S, so they cannot become vacuous through an independent smaller test universe. The
`u+1` cover index matches the existing sibling affine-test locality interface and can
index all open subspaces, including the empty family.

Searches actually run:

- `msearch.py ... leanfinder "Immersion of algebraic spaces is equivalent to being an
  immersion after every affine scheme test and is local on open covers"`: eight hits,
  all scheme notions/locality, including `IsImmersion.instIsZariskiLocalAtTarget`;
  no algebraic-space statement.
- `msearch.py ... loogle "AlgebraicGeometry.IsImmersion,
  AlgebraicGeometry.IsImmersion.isImmersion_iff_exists"`: one hit,
  `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists`, read in full and reused for
  the meaning of scheme immersion. It is not this algebraic-space testing theorem.
- `msearch.py ... grep "AlgebraicSpace|immersion.*affine|IsImmersion"
  AlgebraicGeometry/Morphisms/Immersion.lean`: five hits (scheme immersion class and
  documentation references); no algebraic-space theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `IsRepresentableWith.*IsImmersion|fun _ _ p ↦.*IsImmersion|immersion_affine_tests|immersion.*affine.*test`:
  found existing uses of the same scheme-test specialization in
  `FlatProperPicardAlgebraicSpace` and `LocallySeparatedGroupSpaceScheme`, and proof
  mentions; no declaration of the present statement. This supports reusing the
  existing predicate directly, without a new immersion definition.
- `rg` for `lem-sfb-space-immersion-affine-tests` in `lean/WeilConjectures`:
  no existing declaration. Searches for immersion declarations in
  `lean/Sheaf/AlgebraicGeometry/AlgebraicSpace*.lean` found no competing definition.
- Read the existing sibling `SpaceQuasiCompactAffineTests.lean` to confirm the same
  canonical presheaf-pullback, open-subspace, and joint-surjectivity interfaces.

Validation: `scompile.py O1 lem-sfb-space-immersion-affine-tests` compiled the delivered
file in both sandbox and library module contexts (11.1 s and 8.6 s), cleanly. All three
proofs are `sorry` as required in stage 2; `autoImplicit` is explicitly false and every
universe and variable is bound. There are no statement disputes or node faults.

## Repair of returned delivery 40e2f35f5861

H2: added `def-trf-algebraic-space-jointly-surjective-family` to the item's
`stmt_deps` and added the explicit
`public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`. Read the
owner node's statement and Lean record and the full definition/docstring of
`AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective`: it is exactly the
field-extension lift criterion for joint surjectivity used in the open-cover
equivalence. This records the direct statement dependency previously available
only through the fibre-product module's public re-export. No new node is needed.

Compared the retained sandbox with the returned head described in the return and
the current main node: main still has no `lean` record and its seven statement
dependencies equal those of the returned sandbox. The repaired node differs from
main only in `lean` and the added existing statement dependency. The module changes
only by the requested public import; all signatures, docstrings, proofs and the
complete `lean` record remain byte-identical to the returned delivery. The delivery
wrapper rebases the packet onto current main.

Repair validation: prescribed `scompile.py` compiled the repaired module cleanly in
sandbox and library module contexts (1.9 s and 2.3 s). The requested dependency and
import are the only changes to the node/module relative to the returned version.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
