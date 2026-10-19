## Worker report

The module `Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness` states
`AlgebraicGeometry.valuation_stable_blowdown_uniqueness` with its sole theorem proof
postponed by `sorry`. Three public, fully defined predicates spell out the notions
introduced in this node's own statement. They are listed in `lean.declarations`,
with source and blueprint docstrings. They introduce no independent mathematical
notion beyond that statement, so no new definition node is needed under the
human's helper authorization. No existing statement or definition was changed.

Hypotheses and clauses, checked against the node and the completed module:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The reference k-scheme is `(C : Scheme.{u}) (c : C ⟶ Spec (.of k))`.
  The morphism `r : P.X ⟶ C` is over k by `hr : r ≫ c = P.x`.
  This explicit structural map is used because the statement names the reference map.
- The original pointed curve and terminal pointed curve are `P S : MultipointedCurve
  (Spec (.of k))`. The source and every quotient are semistable by the sequence predicate:
  its zero case includes both endpoint semistability predicates; its successor case
  supplies a semistable elementary contraction and the recursively semistable tail.
- Noncollapse of every connected component is exactly
  `∀ x : P.X, ¬ (r '' connectedComponent x).Subsingleton`. Each connected component
  is the component of one of its points. Negating subsingleton says its image has
  more than one point, without assuming global connectedness or surjectivity onto C.
- `IsReferenceExceptionalComponent k P r a` uses a closed immersion from the existing
  `ProjectiveLine (Spec (.of k))`, requires its structure-map equation and that its
  range belongs to `irreducibleComponents P.X`. This represents the actual reduced
  projective-line component, not an arbitrary projective-line map.
- Its singleton-image clause is `(Set.range (a ≫ r)).Subsingleton`. The range is
  nonempty since the projective line over a field has a rational point; thus this
  is singleton, not an allowance for an empty exceptional component.
- The special-point bound is the encard of the intersection with
  `Set.range P.i ∪ {x | x ∉ P.x.smoothLocus}`, bounded by 2. It counts distinct
  points of the component, not branches of its normalization or marking lengths.
- `Hom.IsReferenceExceptionalContraction` requires source and target semistability,
  `IsIso f.marking`, and `f.curve ≫ s = r`. The existential component is exceptional
  for that current reference map. `IsPushout a (ProjectiveLine ... ↘ Spec ...) f.curve b`
  is the actual scheme pushout in the node, and `b ≫ Q.x = 𝟙 _` makes the scalar vertex
  compatible with the base. The pair's existing `Hom.comm` transports the marking.
  No properness, connectedness or isomorphism-off-the-component hypothesis was added.
- `Hom.HasReferenceExceptionalContractionSequence k n` recursively composes such
  elementary contractions, including equality with the supplied curve AND marking maps.
  Every recursive quotient uses its own marking, nonsmooth locus and induced reference
  map. The zero case requires both maps to be isomorphisms, so an arbitrary final
  pointed isomorphism is permitted, including a genuinely empty contraction sequence.
  The reference map on the last quotient is retained in the zero-case equation.
- `hπ` is the supplied terminal finite sequence; `hstable` excludes every exceptional
  component on its target for the induced map `s`. Semistability and reference
  compatibility are part of the sequence, rather than additional restrictions.
- The first conclusion quantifies over every quotient Q, induced reference t, map q,
  length m and supplied sequence. `∃! v : Q.Hom S` with both composition equations
  says exactly that there is a unique pointed k-morphism with π = v q. Morphisms
  include their base and marking compatibility in the recorded `MultipointedCurve.Hom`.
- The second conclusion quantifies over a second terminal sequence and asserts a unique
  compatible pointed morphism with `IsIso v.curve ∧ IsIso v.marking`. A morphism of pairs
  invertible on both parts is precisely an isomorphism of pointed curves; its inverse
  satisfies both compatibility squares. Thus this renders the unique-isomorphism clause.
- Neither curve structural map is required to be proper, separated, or connected.
  Properness is not smuggled into the definition of elementary contraction. The theorem
  assumes the actual finite terminal sequence; it does not assert its existence.

Dependency interfaces read and used:

- `Sheaf.TraceFormula.MultipointedCurve`, `AlgebraicGeometry.MultipointedCurve`: the
  existing flat, finitely presented pure-dimensional curve and marking, closed immersion.
- `Sheaf.AlgebraicGeometry.MultipointedCurveModification`,
  `AlgebraicGeometry.MultipointedCurve.Hom` and `.IsSemistable`: the existing paired
  morphisms and semistability; their full source was read, including geometric fibres.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`,
  `AlgebraicGeometry.ProjectiveLine.TwistData`, and its underlying
  `AlgebraicGeometry.ProjectiveLine` in `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  this node uses only the recorded projective line, not the twisted-sheaf data.
- Mathlib `Field`, `IsAlgClosed` (the algebraic-closure node's explicitly recorded
  algebraically-closed predicate), `Scheme`, `Spec`, `connectedComponent` and
  `ConnectedSpace`; signatures and docstrings read in their recorded source modules.
- Mathlib `CategoryTheory.Limits.IsPushout` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`, whose colimit field
  is the recorded `IsColimit` universal property of `def-weil-pbc-category-colimit`.
  The recorded `Cocone`, `IsColimit`, and chosen colimit signatures were also inspected.

The only genuine nondefinition proof dependency is
`lem-trf-exceptional-contraction-diamond`. Its current DAG record has no Lean module
or declaration, so no import can be added yet; the proof docstring explicitly retains
its role (noncollapse persistence and two-component diamonds). The other proof dependencies
are imported through the public projective-line and pushout interfaces. No missing notion
needed by the present theorem statement is left unstated.

Source read: Temkin arXiv 0707.3953v3, Appendix B, printed p. 58, including the paragraph
before Lemma B.3 and its final factorization assertion. The PDF was retrieved into the
item's scratchpad and read as text. The source's proper-surjective connected-curve setting
explains the node's already-reviewed noncollapse condition; this delivery does not change
that reviewed statement or claim the unqualified constant-reference version. Its six-step
induction/cancellation proof is carried in the theorem docstring, with every DAG proof step.

Edge cases checked: n=0 and m=0 retain arbitrary final pointed isomorphisms; empty marking
has an isomorphic empty marking under each contraction; the empty curve has no connected
components or projective-line components and only zero-length sequences. Disconnected,
nonproper and nonseparated curves are not excluded by any added hypothesis. The unmarked
two-gon with constant reference fails the explicit noncollapse hypothesis, as required by
the existing stage-1 correction. No characteristic restriction is imposed. Component images
are nonempty, making the subsingleton/singleton formulation equivalent. All variables and
the universe are explicitly bound with `autoImplicit false`.

Searches for an existing statement/notion:

- `msearch.py leanfinder`, query "A stable blowdown of a semistable multipointed curve
  is unique and factors uniquely through every finite exceptional contraction sequence":
  eight hits, including valuative-criterion uniqueness, normalization hom extensionality
  and rational maps; none concerns pointed semistable-curve contraction sequences.
- `msearch.py loogle`, query `"contraction"`: twelve hits concerning polynomial separable
  contractions and compiler eta contraction, no scheme blowdown statement.
- `msearch.py grep`, query `blowdown|exceptional.*[Cc]ontraction|semistable` in
  `AlgebraicGeometry`: zero Mathlib hits.
- `rg` of the upstream `WeilConjectures` tree for the item id and for blowdown,
  exceptional contractions and semistability: no matching theorem. The upstream name
  index was searched too; no matching declaration.
- `rg` of `lean/Sheaf` found the landed
  `MultipointedPair.HasExceptionalContractionSequence` in
  `Sheaf.TraceFormula.SemistableModificationFibreContractions`. Its complete definition,
  docstring, owning node and current server source were inspected. It is relative to
  its final quotient Q, includes properness and a complementary-open isomorphism, and
  uses underlying raw pairs. The present node has a separate arbitrary reference C and
  does not assume those extra conditions. Specializing that interface would lose cases;
  the present helpers express the distinct reference-relative notion on the recorded
  `MultipointedCurve`, retaining its smooth-locus interface. The existing definition
  and its owning theorem are not redefined or repaired.
- DAG search for elementary contractions, contraction sequences and stable blowdowns
  found this node, the diamond lemma, the fibre-contraction lemma and their consumers.
  None independently owns the separate-reference predicates newly made explicit here.
- Full new declaration names were searched in the project and upstream; none exists.

Validation: required `scompile.py NG lem-trf-valuation-stable-blowdown-uniqueness` compiled
both its sandbox and actual library module without errors or warnings (3.0 and 3.2 seconds).
No theorem was proved, no data was chosen through a postponed theorem, and there is no
new statement dispute or correction. The inherited stage-1 report describes a superseded
constant-reference formulation; the current noncollapse formulation is the one stated here.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
