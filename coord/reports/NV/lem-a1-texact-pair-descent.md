## Worker report

The module `Sheaf.CategoryTheory.Triangulated.TExactPairDescent` states
`CategoryTheory.CommonStage.tExactPairDescent`, with its only theorem proof `sorry`.
There is no statement correction and no disputed mathematical assertion. Its three data
helpers have real data: `triangleImageOne` is the literal image triangle of Stacks 014V;
`ExactPairDiagram` and `ExactPairPresentation` bundle precisely the supplied structures
and hypotheses. They introduce no alternative pair-category construction. The existing
`CommonStage` quotient and canonical operations remain the objects of the assertion.

Hypothesis and conclusion correspondence:

* A prime ell, a fixed algebraic closure Omega, and its finite intermediate fields are
  `(l : ℕ) [Fact l.Prime]`, the `Field`, `Algebra`, `IsAlgClosure` binders on Omega,
  and `Padic.FiniteCoefficientFields l Ω`. No nonempty or directed instance is assumed:
  those are mathematical properties of this specific index, used by the proof dependency.
* For the two diagrams, `ExactPairDiagram` extends the recorded `CommonStage.Diagram`.
  Its category, preadditive, biproduct, transition, additive, unit, associator, unit-law,
  and pentagon fields are inherited verbatim. Its `shift`, `zero`, `shift_additive`,
  `pretriangulated`, `triangulated` fields are the Mathlib triangulated-category data;
  `t` and `bounded` are the bounded t-structures. Its `s`, `exact`, `le`, `ge` are the
  selected transition comparisons and exactness and preservation of both halves at zero.
  There is no assumption of associator compatibility with shifts or faithfulness.
* `RA`, `RB` use the dependency's `PairStructure`, with Hom exactly its `Quot` of
  common-stage representatives modulo eventual equality. `P.canonical`, `Q.canonical`
  impose exactly equality after transport and the common-stage identity, composition,
  addition, zero and negation laws. The transport uses the specified associator inverse
  on the source and associator on the target, exactly as in the node.
* The pair-category triangulated instances are supplied in the theorem binders.
  `P.J`, `P.obj`, `P.map` (and Q) specify the stage inclusions, including the normalized
  identity-field map. `shift_obj`, `shift_map` prescribe the induced one-step shift
  object and representative formulas. `j` with `j_identity` names the identity-field
  shift identifications; it does not allow an arbitrary comparison. `triangles` is an
  iff with the isomorphism closure of distinguished finite-stage triangles. `t`,
  `bounded`, `le`, `ge` are exactly the assumed bounded t-structure and the two
  isomorphism-closure descriptions at zero.
* `Φ : Family A.toDiagram B.toDiagram` provides the additive stage functors and the
  specified b comparisons. `hb : Φ.Coherent` is exactly the normalized unit and
  associator tower equation. `c` is the selected natural comparison for shift by one;
  `hExact` is exactness with this precise comparison, and `hLE`, `hGE` are stage
  t-exactness. `hShift` is the node's shift square expanded in Lean composition order:
  V(c_E) then sD then b[1] equals b at X[1] then F(sC) then c_L.
* `∃ F, IsDescent RA RB Φ F` says the formulas define an additive functor, including
  `F(E,X)=(E,F_E X)` and the map of every representative as b_source then F(u) then
  inverse b_target. Because the Hom domain is the existing quotient, this is independent
  of representatives and common field. This uses no faithful-transition hypothesis.
* `γ` is a natural isomorphism for shift by one. Its component HEq is exactly the
  inclusion of c at the original stage. HEq only accommodates the previously specified
  object and shift equalities. The next clause states preservation of distinguished
  triangles using exactly γ. The cutoff clause preserves both `le n` and `ge n` for
  all integers n, so expresses the full t-exactness assertion.
* The next clause states each inclusion is additive, sends distinguished triangles to
  distinguished triangles with its prescribed identity comparison, and preserves both
  halves at every integer cutoff, for each of the source and target diagrams.
* The literal equality `P.J i ⋙ F = Φ.φ i ⋙ Q.J i` is the node's stage equality.
  The identity-component `κ` identifies these same composites and its explicit square
  is their shift compatibility. The final representative HEq evaluates F on the
  canonical extension arrow: it is represented by b at the larger field, with the
  normalized identity-field identifications written as `eqToIso` transports. These
  transports are forced by `A.unit`, `B.unit`, rather than extra comparison choices.
  Naturality is the naturality of b; its extension tower and shift square are already
  the hypotheses `hb.tower`, `hShift` (the six-step proof explains this final assertion).

Dependencies read and used:

* `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`, `Padic.FiniteCoefficientFields`,
  `finiteCoefficientCompositum`, `finiteCoefficientBase`, and their property theorem.
* Mathlib `CategoryTheory.Pretriangulated`, `CategoryTheory.IsTriangulated`, and
  `CategoryTheory.Triangulated.TStructure` with its `bounded` object property. Read their
  complete definitions, including ambient instances and t-structure strict-full fields.
* Mathlib `AddCommGroup.DirectLimit` with `of`, `of.zero_exact`, and `lift`; the existing
  `CommonStage` quotient is its common-stage presentation, rather than a second limit.
* `Sheaf.CategoryTheory.StageSystemFunctorDescent` publicly reexports
  `Sheaf.CategoryTheory.CoherentPairFunctorDescent`. The original generic interface
  `CommonStage.Diagram`, `PairStructure`, `PairStructure.IsCanonical`, `Family`,
  `Family.Coherent`, `IsDescent` is used. Read its declarations and proof documentation,
  and the newer StageSystem transport interface. The original interface applies here:
  the item starts with arbitrary supplied pair structures, not a fixed StageSystem.
  This already landed dependency was added to stmt_deps since its data types occur in
  the statement, as permitted for an existing landed node by brief-stage2 section 5.

Sources read locally: Stacks `derived.tex`, definition-exact-functor-triangulated-categories
(014V), including the paragraph on exact natural transformations; `algebra.tex`,
lemma-directed-colimit (00D6); sketch 42, the pseudocone functor and exactness propositions.
The complete six-step node proof is reproduced in the theorem docstring.

Edge cases checked: the constant one-stage diagram gives the original functor and its
selected shift comparison; zero categories and zero functors satisfy the formulas;
nonfaithful transitions that kill a morphism still respect eventual equality. Repeated
fields use the given unit equalities, and no inverse faithfulness argument is used.
Every integer cutoff, including zero and negative integers, occurs in the conclusion;
only preservation at zero is assumed, extended using the natural shift comparison.
The finite-field index is inherently nonempty, so an extraneous empty-index case has not
been introduced. Carrier and Hom universes u and v are independent; using their common
upper universes for the two category diagrams is the existing generic interface's size
encoding and imposes no equality of object and Hom universes.

Searches (msearch results are also in the sandbox searches.jsonl):

* LeanFinder: “A coherent family of t exact functors on triangulated categories descends
  to common stage pair categories preserving triangles and t structures”; eight hits,
  including `Functor.map_distinguished_exact`, localization criteria and image-triangle
  lemmas. None states this common-stage descent, inclusion, and t-exactness theorem.
* Loogle: first `Functor.IsTriangulated, TStructure` returned an unknown-identifier
  diagnostic; retried with `"Functor", "IsTriangulated"`, twelve hits giving the
  functor class, identity and composition instances, and exactness transport, no match.
* msearch grep: `pairFunctor|PairCategory|TExact` in CategoryTheory, 25 capped hits,
  primarily GuitartExact/short-exact material, no matching assertion.
* rg of `lean/WeilConjectures` and `lean/Sheaf` for pair t-exactness, common-stage diagrams
  and the item's exact blueprint id; inspected `StageSystemFunctorDescent`,
  `CoherentPairFunctorDescent`, `DirectedPairBoundedTStructure`, and
  `PbcPairFunctorShiftCoherence`. None states this theorem. The latter assumes additional
  shift/associator compatibility and is PBC-specific, so cannot replace this item.
* `tools/blueprint_refs.py search 'pair category'` found eight blueprint notions, chiefly
  scheme-specific PBC categories. The generic coherent descent dependency is the usable
  existing notion. Exact-name rg for all four proposed declaration names found no clash
  in Mathlib, WeilConjectures or Sheaf.

Validation: prescribed scompile.py compiles the delivered module in sandbox and library
mode. Only the expected sorry theorem warning is permitted. No direct build or Git command
was run in the shared repository, and all authored files are in the assigned sandbox.

## New nodes

`def-a1-common-stage-pair-functor-data` records ownership of the generic declarations already provided by `Sheaf.CategoryTheory.CoherentPairFunctorDescent`: `CommonStage.Diagram`, `Pair`, `Rep`, `transport`, `EventuallyEqual`, `Hom`, `repr`, `PairStructure` and its `Obj`, `repr`, and `IsCanonical` data, `pairCategory`, `pairPreadditive`, `Family` and its `Coherent`, `obj`, and `rep` data, and `IsDescent`. The node is an existing-definition attachment, with no new Lean file. Its statement dependency is the universe convention node. The Mathlib searches found only unrelated pairwise/gluing declarations and no matching common-stage interface. The item now cites this definition node in `stmt_deps`; `lem-sbc-coherent-pair-functor-descent` remains in `proof_deps` and in proof Step 1.

## Second reading by NV

I reread the node and module clause by clause in this same worker; no other agent was
started, following the dispatcher instruction. The maintainer's independent delivery
review remains the independent reading. This reread found two interface details and
repaired them: an unnecessary explicit identity-stage shift hypothesis was removed,
and the literal stage-functor equality was added alongside its identity-component natural
isomorphism, matching the node's equality wording exactly. The shift square's direction
was checked against the dA/dB calculation in proof Step 2. The extension representative
was checked with both normalized identity transitions: its source identity map has target
U_{j/j}(U_{j/i}X), hence the inverse eqToIso is required; its target expression is b followed
by the inverse target identity-field eqToIso. Both triangles and halves use iff with
isomorphism closures, not just one-sided implications. Every hypothesis and conclusion
is matched above; no node statement, proof or proof_deps changed.
