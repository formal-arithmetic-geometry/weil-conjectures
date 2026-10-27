## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceQuasiCompactImmersionLocality` states
`AlgebraicGeometry.AlgebraicSpace.quasiCompactImmersion_iff_fppfCover` with proof `sorry`.
It introduces no definitions. The node statement and all dependency lists are unchanged.
The source is Stacks, spaces-descent.tex, Tag 0424,
`lemma-descending-property-quasi-compact-immersion` (read at lines 1722–1751).

Hypotheses and clauses, in the order of the node:

- A scheme S: `{S : Scheme.{u}}`, using Mathlib's `AlgebraicGeometry.Scheme`.
- Algebraic spaces Z and T over S and their morphism h: `{Z T : AlgebraicSpace S}`
  and `(h : Z ⟶ T)`. The published space category is the full subcategory of fppf
  sheaves with representable diagonal and a surjective étale scheme atlas. Its maps
  are natural transformations; `h.hom.hom` is exactly the underlying presheaf map.
- A family of algebraic spaces over T: `{I : Type w}`, `(Tᵢ : I → AlgebraicSpace S)`
  and `(q : ∀ i : I, Tᵢ i ⟶ T)`. The index universe w is independent of u, so no
  cardinality restriction or nonemptiness assumption is added.
- The family is fppf: `(hq : IsFppfCover q)`. This is the existing definition in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus`, not a new predicate.
  Reading its definition and its dependencies shows it means chartwise flatness,
  chartwise local finite presentation, and joint surjectivity on field-valued point
  classes. This is the node's fppf condition on étale scheme charts after scheme
  base change; no representability of q or scheme source for q is imposed.
  The published `isFppfCover_pullback` and `isFppfCover_scheme_iff` state its base
  change and agreement with `Scheme.fppfPrecoverage`. That precoverage is the
  jointly surjective flat locally finitely presented scheme precoverage of the
  recorded dependency `def-pc-fppf-site`.
- h is a quasi-compact immersion:
  `IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left ∧ IsImmersion p.left)
  h.hom.hom`. The existing `IsRepresentableWith` quantifies over every scheme
  `W : Over S` and every `yoneda.obj W ⟶ T.obj.obj`. It supplies an actual scheme
  `U : Over S`, projection `p : U ⟶ W`, and an `IsPullback` square of presheaves,
  together with both properties of its projection. Thus scheme representability
  is part of the conclusion, rather than a hypothesis.
- An immersion factors closed then open: the predicate `IsImmersion p.left` is
  precisely equivalent to that factorization by the read Mathlib declaration
  `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists` in
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`. Its factors are the recorded
  `IsClosedImmersion` and `IsOpenImmersion`; the module imports them through this
  Mathlib module. No alternative meaning of immersion is introduced.
- Quasi-compactness uses Mathlib's `QuasiCompact p.left`: inverse images of
  quasi-compact opens are quasi-compact. Requiring this on every representing
  scheme test is equivalent to quasi-compact source for each quasi-compact test
  scheme: the forward direction tests the whole quasi-compact target; conversely,
  test each quasi-compact open of any target scheme. This uses no separation
  hypothesis. It is the representable specialization of the node's condition,
  compatible with the existing
  `quasiCompact_iff_representableWith_quasiCompact`. Compactness throughout is
  `CompactSpace` / `IsCompact`, with no Hausdorff assumption, as in the recorded
  `def-weil-pbc-quasi-compact-scheme`.
- The equivalence is `↔`; the right side quantifies `∀ i : I` and applies exactly
  the same predicate to `Limits.pullback.snd h.hom.hom (q i).hom.hom`. This is
  the actual projection from the presheaf fibre product Z ×_T Tᵢ to Tᵢ. Sheaf
  inclusion preserves these limits, so it is also the underlying map of the
  algebraic-space fibre product. This formulation needs no chosen atlas or
  arbitrary comparison map.
- The last sentence about descent of representability is included in the left
  side's `IsRepresentableWith`: no `IsRepresentable h.hom.hom` assumption occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, `IsAlgebraicSpace`.
  Their signatures and docstrings were read in full.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; the over-S site is the existing `.over S`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- The already published covering definition comes from the existing node
  `lem-sfb-space-fppf-covering-calculus`, its owning module named above.
  Its chart predicates `MapIsFlat`, `MapIsLocallyOfFinitePresentation`, and
  `IsJointlySurjective` were read in AlgebraicSpaceMorphismProperties.lean and
  AlgebraicSpaceJointSurjectivity.lean.

The proof docstring gives all five accepted proof steps, including finite coproducts,
affine scheme tests, quasi-affine representability descent before scheme immersion
descent, the fpqc criterion, and the fppf-to-fpqc specialization. Available proof modules
are imported without `public`: QuasiCompactImmersionAffineDescent,
SpaceQuasiAffineAffineDescent, SpaceQuasiCompactAffineTests, AlgebraicSpaceCoproduct,
FppfSheafCoproductPartition, and Mathlib Morphisms.QuasiSeparated. The remaining
Mathlib proof inputs occur in these imports or the public Immersion module.
`lem-sfb-space-fpqc-property-affine-criterion` and
`lem-sfb-space-immersion-affine-tests` have no Lean record in the read DAG, so no
invented module import is given for them. They are proof inputs only, not missing
notions required to state this theorem. No missing statement dependency was found.

Edge cases checked before drafting and again on reading:

- Empty I: IsFppfCover forces T empty (as stated by the existing covering-calculus
  empty-index theorem). Then a morphism Z → T forces Z empty. The right-hand side
  is vacuous and h is the empty isomorphism, hence a quasi-compact immersion.
- Empty members, empty Z, and empty base S are allowed; no Nonempty or positivity
  assumptions occur. Surjectivity is joint, not required of individual members.
- Arbitrary, non-quasi-compact and nonseparated targets and covering members remain
  allowed. No source, target or member is assumed a scheme or quasi-compact.
- No Noetherian, finite-type or characteristic hypotheses occur in the source or
  the Lean statement. Only the covering maps have the required flat and locally
  finitely presented chart properties.
- A quasi-compact open immersion need not be closed: D(2) → Spec Z is permitted.
  The source's phrase “closed immersion” in its proof is a typo already explained
  in the accepted split; the actual lemma and this statement both say immersion.

Searches for an existing statement (full machine outputs in searches.jsonl):

- msearch LeanFinder: “A quasi compact immersion of algebraic spaces is local on
  the target for fppf coverings”: 8 hits, all scheme covering/descent/factorization
  facts, including IsImmersion.isImmersion_iff_exists_of_quasiCompact; no match.
- msearch Loogle: `"IsImmersion", "DescendsAlong"`: 0 hits.
- msearch grep: `AlgebraicSpace|IsImmersion.*(DescendsAlong|fppf|fpqc)` in
  AlgebraicGeometry: 0 hits.
- msearch LeanSearch: “Quasi compact immersion algebraic spaces fppf local on the
  target”: 8 hits about scheme quasi-compactness, scheme descent and quasi-affinity;
  no algebraic-space locality theorem.
- rg in lean/WeilConjectures/AlgebraicGeometry for AlgebraicSpace, immersion,
  quasi-compact immersion and 0424: scheme statements only, no match. The required
  item-id search there returned none. dag/lean_names_upstream.json likewise has
  scheme immersion factorization but no matching algebraic-space statement.
- rg in lean/Sheaf/AlgebraicGeometry for IsRepresentableWith, IsImmersion,
  FppfCover, fppf covering and 0424: found and reused IsRepresentableWith,
  IsFppfCover and scheme immersion; the Picard module uses representable
  immersions, but no existing theorem states the requested equivalence.

No STATEMENT-DISPUTED flag, statement correction, new definition node or dependency
repair is needed. All variables and universes are explicitly bound; autoImplicit is false.
The server compile through scompile.py passed both sandbox (8.7 s) and actual library
module (4.2 s), with no errors or warnings.

## Second reading by Q32

This is a separate final reading by the same worker, since the dispatcher's explicit
instruction prohibits starting other agents; the maintainer's independent review remains
separate. I reopened the node, the delivered module and Stacks Tag 0424.

S, Z, T, h and the arbitrary family are exactly the original objects. The covering
hypothesis is the published chartwise fppf definition, includes joint surjectivity,
and adds neither representability nor quasi-compactness of its members. The left-hand
side's scheme-test pullback witnesses encode representability and both quasi-compactness
and immersion together. The latter means the recorded closed-then-open factorization;
the former agrees with the CompactSpace condition for all quasi-compact scheme tests.
The right-hand side uses the canonical second projection of the fibre product in the
correct order (h first, q_i second) and the identical predicate. The biconditional and
unrestricted universal quantifier render both directions and every covering member.
No extra finiteness, separation or nonemptiness assumptions were found. In particular
the nonrepresentable-downstairs and empty-family cases have not been removed.

The source's proof typo is only documented; no node correction is warranted because
the node already states the true source lemma. The five proof steps and their uses are
all recorded in the declaration docstring. There are no local notation or instances,
no helper declarations and no proofs beyond sorry. No mismatch was found on this reading.
