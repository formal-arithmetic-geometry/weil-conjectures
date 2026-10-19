## Worker report

This is a repair delivery for the previously reviewed stage-2 interface of
`lem-coef-extreme-bimodule-attachment`.  The theorem and the two real helper
constructions remain in `Sheaf.CategoryTheory.ExtremeBimoduleAttachment`.  The
repair adds the two clauses that the returned review identified as necessary:
the replacement diagram `V'` preserves the `S` block labels, and its backwards
mapping simplicial sets are degreewise empty, so `V'` is directed on the same
blocks.  The existing corrected node statement, its `statement_change`, proof,
and dependency list are retained.  The theorem proof is only `sorry`; the
helper definitions contain no postponed data.

The module's declarations are:

* `CategoryTheory.ExtremeBimoduleAttachment.MappingPushoutSquare`, which stores
  the actual simplicial mapping-space cocone, identifies its apex with the
  mapping set of the cocone target, and identifies both legs with the actual
  enriched cocone maps.
* `CategoryTheory.ExtremeBimoduleAttachment.CoconeConclusion`, which states
  that the extreme mapping square is a derived homotopy pushout and that every
  nonextreme mapping set is a weak homotopy equivalence.
* `CategoryTheory.ExtremeBimoduleAttachment.extreme_bimodule_attachment`, the
  repaired statement theorem.

Hypothesis and conclusion audit (the names below are the theorem binders).

* `N : CoherentNerveComparisonStatement.{u}` supplies the recorded Bergner model
  structure and its Dwyer--Kan weak-equivalence class; no second model structure
  is introduced.
* `I` has `LinearOrder`, `Finite`, and `a < b`; `ha` and `hb` state that `a` and
  `b` are the least and greatest labels.  Thus the finite ordered index and its
  distinct endpoints are explicit.
* `S : Set I` with `haS` and `hbS` is the labelled subset containing both
  endpoints.  `O : J → I → Type u` supplies disjoint blocks through dependent
  sums `Σ i : I, O j i` and `Σ i : S, O j i.val`; no block is assumed inhabited.
* `T B V : J ⥤ SCat.{u}` and `eT`, `eB`, `eV` identify the object sets with the
  indicated sums.  `g_objects` is inclusion of the `S`-labelled objects and
  `f_objects` is identity on them.
* `T_blocks`, `B_blocks`, and `V_blocks` require every diagram transition to
  preserve labels.  `T_directed`, `B_directed`, and `V_directed` say that every
  backwards mapping simplicial set is degreewise `IsEmpty`, exactly the directed
  condition.  The new `eV'` clauses repeat the label preservation and backwards
  emptiness for the replacement diagram itself.
* `f_weak` is the weak homotopy equivalence of `f` on every pair except the
  ordered extreme pair `(a,b)`.  `g_endpoints` is precisely the disjunction of
  the two endpoint-block cases `(a,a)` and `(b,b)`.
* The conclusion factors `f` as `f = j ≫ p` with `V'`, `j`, and `p`.  Each
  component `p.app k` is a Bergner weak equivalence and is a componentwise weak
  homotopy equivalence on every mapping simplicial set.  `eV'` identifies the
  replacement objects with the same `S` blocks, and the two equations specify
  the object maps of `j` and `p`; the repaired clauses make the replacement
  diagram directed and label preserving.
* For every `Z`, `iB`, and `iV'` with the strict cocone equation
  `g ≫ iB = j ≫ iV'`, and with the recorded
  `CofibrantSimplicialInversion.IsBergnerHomotopyPushout` condition in every
  component, `CoconeConclusion` gives the canonical extreme mapping square and
  the nonextreme weak equivalences.  `MappingPushoutSquare` keeps the actual
  cocone maps by `HEq`; its `IsDerivedLimit` condition is the derived-colimit
  (homotopy-pushout) condition in spaces and imposes no Kan hypothesis.
* A second existential supplies a representative `Z` with the full `I`-labelled
  object sum, the strict cocone and homotopy-pushout property, the two object-map
  equations, and label preservation under every transition in `J`.  Quantifying
  over arbitrary `J` and all these natural transformations renders the stated
  naturality for block-preserving maps, including maps identifying objects inside
  a block.  The singleton category recovers an individual span.

The statement correction already present in the base node is retained.  It
replaces the false demand for a strict homotopy-pushout cocone over the original
`f` by the cellular factorization `f = j ≫ p`, with `p` a Bergner weak
 equivalence, and uses the strict cocone over `j`.  The two-block test with
`T(x,z)=S⁰` and `B=V=[1]` gives an ordinary pushout mapping space `*` but a
homotopy-pushout mapping space `S¹`, so the old strict-cocone formulation cannot
hold.  The existing citer `lem-coef-directed-three-face-mapping-pushout` still
holds after replacing its right leg by `j` and then comparing via `p`; it is not
edited.

Dependency declaration read: `CategoryTheory.coherent_nerve_comparison` in
`Sheaf.CategoryTheory.CoherentNerveComparison`, together with the recorded
`CoherentNerveComparisonStatement`, `BergnerModelData`, and its
`weak_iff_dwyer_kan` field.  The full source signature and docstrings were read.
The proof imports used by the module include the published
`CofibrantSimplicialInversion.IsBergnerHomotopyPushout`,
`SimplicialLocalizationCalculus.IsDerivedLimit`, the Kan--Quillen weak
 equivalence structure, fixed-object free-arrow/pushout comparison, the
fixed-object simplicial calculus, model-colimit comparisons, the arrow-cell word
filtration, Bergner left properness, realization finite limits, and filtered
simplicial-set gluing equivalences.  No dependency declaration is redefined.

Edge cases checked: `I` has at least the two endpoints, while any intermediate
block may be empty; `S` may have no other labels.  Empty endpoint blocks make the
extreme quantifier vacuous, and empty mapping simplicial sets remain allowed.
The theorem imposes no `KanComplex`, `IsLocallyKan`, or cofibrancy hypothesis on
`T`, `B`, `V`, `V'`, or `Z`.  The singleton indexing category, an empty indexing
category, and transition functors identifying objects inside a block are all
covered by the diagram quantifiers.  Pairs `(b,a)`, `(a,a)`, and all pairs in
intermediate blocks remain in the directed/nonextreme clauses.

Searches made for an existing declaration or duplicate notion:

* `msearch.py ... leanfinder "homotopy pushout of small simplicial categories
  directed blocks extreme mapping square weak equivalence"` returned only generic
  attachment and pushout declarations; no match.
* `msearch.py ... loogle "BergnerModelData, IsBergnerHomotopyPushout,
  IsWeakHomotopyEquivalence"` returned zero hits because `BergnerModelData` is
  not a Mathlib identifier.
* `msearch.py ... grep "Bergner|homotopyPushout|directed" CategoryTheory`
  returned generic Mathlib directed and pushout results only.
* `rg` over the upstream `WeilConjectures` checkout found no declaration or
  blueprint-tag match.  `rg` over the shared `lean/Sheaf` tree found only this
  item's existing module.  No Mathlib or upstream declaration states this
  enriched extreme-pair assertion.

Validation: `scompile.py N7 lem-coef-extreme-bimodule-attachment` compiled the
sandbox check and the library module with exit status 0, no errors, and no
warnings.  The final signature in the node's `lean.statement` was generated by
`tools/stage2_delivery.py signature` from the repaired theorem through `:=`.

## Second reading by N7

I reread the corrected node and the repaired module together.  Every original
hypothesis appears once: finite linear order with least/greatest endpoints,
labelled object sums, directedness, block-preserving diagram maps, the two
mapping-equivalence assumptions, and the absence of any local Kan condition.  I
checked the returned interface point directly: the `eV'` conjunction now states
both `(eV' l ((V'.map α).obj x)).1 = (eV' k x).1` and degreewise emptiness for
backwards `V'` mapping sets.  The factorization uses the strict cocone over `j`
while `p` compares it to the original `f`; no strict cocone over the false old
formulation is reintroduced.  The extreme square retains the two actual cocone
maps and its derived-limit predicate, and the representative retains the full
object sum and naturality equations.  The repaired file compiles cleanly under
the prescribed wrapper.

## Statement corrected

This section records the inherited §1(C) correction, which remains in the node.
It supplies the explicit report heading and complete audit required by
coord/brief-stage2.md §6 and delivery-errors H7.

### Old statement (verbatim from statement_change.old_statement)

Use small simplicial categories, weak homotopy equivalences and the Bergner model structure of [lem-coef-coherent-nerve-comparison]. Let $I$ be a finite linearly ordered set with distinct least and greatest elements $a<b$, let $(O_i)_{i\in I}$ be disjoint small sets, and let $S\subseteq I$ contain $a,b$. A category directed by these blocks has the indicated object set and has empty mapping sets from $O_j$ to $O_i$ when $i<j$. Let $B$ be directed on $I$, and let $T,V$ be directed on $S$. Let $g:T\to B$ and $f:T\to V$ be enriched functors preserving the block labels, equal on objects to the inclusion and identity respectively. Suppose that $f:T(u,v)\to V(u,v)$ is a weak homotopy equivalence unless $u\in O_a,v\in O_b$. Suppose also that $g$ induces weak homotopy equivalences on all mapping sets within $O_a$ and within $O_b$.

For the homotopy pushout $Z=B\amalg_T^h V$ in the Bergner model structure, with its specified cocone maps, the canonical square
$$\begin{array}{ccc}T(x,z)&\longrightarrow&V(x,z)\\ \downarrow&&\downarrow\\ B(x,z)&\longrightarrow&Z(x,z)\end{array}$$
is a homotopy pushout of spaces for $x\in O_a,z\in O_b$. Here homotopy pushouts mean derived colimits of the respective spans, with their maps. The cocone map $B\to Z$ induces a weak homotopy equivalence on every other mapping set. The object set of a representative of $Z$ can be taken to be $\coprod_{i\in I}O_i$. All comparisons are natural for maps of such diagrams preserving blocks and cocones. Empty blocks and mapping sets are allowed, and no local Kan hypothesis is imposed.

### Defect and corrected meaning

The original existential conjunct required a strict homotopy-pushout cocone for the given map f:T→V. This is false: for I={a<b}, O_a={x}, O_b={z}, T(x,z)=S⁰, T(x,x)=T(z,z)=pt, T(z,x)=∅, and B=V=[1] with g=f the collapse, the ordinary pushout is [1] while the homotopy-pushout mapping space is S¹, so no such strict cocone over f exists. The corrected statement uses the cellular factorization f=j≫p with p a componentwise Bergner weak equivalence and asserts the strict cocone and mapping square for j, together with the weak equivalence V′(x,z)→V(x,z).

The replacement retains the intended derived mapping-space assertion. It does
not assume a strict derived-pushout cocone over the unmodified right leg.
For the declared types `j : T → V'` and `p : V' → V`, the factorization is
`f = j ≫ p` in Lean, or `f = p ∘ j` with conventional function-composition
notation. The prose node's `f = j ∘ p` uses diagrammatic order; its meaning is
fixed by these types, the displayed factorization in proof step 3, and the
existing statement_change. No mathematical or Lean statement is changed here.

### Source and citer audit

Source: https://www.math.ias.edu/~lurie/papers/HTT.pdf — Appendix A.3.2--A.3.3 as background; the correction follows the cellular replacement and derived-colimit comparison in proof steps 3--6 of this agent-formulated auxiliary assertion.

The local blueprint source
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`,
paragraph 2, concerns the derived coefficient adjunction. It does not purport to
state the extreme-attachment assertion. HTT A.3.2.4 (including its word
filtration), A.3.2.18, and A.3.3.1–2 provide the enriched model-category
background. The factorization and mapping-space claim are the agent argument
in the item's twelve proof steps, rather than a quoted HTT theorem.

- `lem-coef-directed-three-face-mapping-pushout`: holds. Read its statement and
  proof, especially steps 2 and 6–9. Step 7 uses `I={0,1,2,3}` and
  `S={0,2,3}`. Its extreme mapping square is preserved by replacing the right
  leg with `j`, applying the attachment statement, and comparing via the
  mappingwise weak equivalence `p`. The strict face cocone may also be
  precomposed with `p`; the resulting map of spans is objectwise weakly
  equivalent, hence gives the same derived pushout. The comparisons keep the
  actual inclusions, including the map from the 03 edge. Step 9's nonextreme
  maps remain weak equivalences by two-out-of-three. No citer is edited.

A search of the group clone's `dag/nodes` found this single direct citer in
`stmt_deps` or `proof_deps`; there is no second direct citer to inspect.
The inherited `old_stmt_deps` is
`["lem-coef-coherent-nerve-comparison"]`; the current four dependencies add
precisely the homotopy-pushout, derived-limit and Kan–Quillen interfaces used
by the Lean statement. The existing statement_change history is retained.

### Independent maintainer verification of this repair delivery

The immutable module was read against the node, all four statement-dependency
nodes, the exact imported declarations, and the sources above. The repaired
`eV'` conjunction includes both preservation of labels under every diagram map
and degreewise emptiness of reverse mapping sets. The strict cocone conclusion
uses the actual enriched mapping maps, through `MappingPushoutSquare.left` and
`.right`, and the nonvacuous derived-colimit predicate in `CoconeConclusion`.
The existential representative has the full `I` object sum. No additional Kan,
cofibrancy, nonemptiness, or endpoint equivalence assumptions are imposed.

Reproduced compiler command against the immutable file:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py N7 lem-coef-extreme-bimodule-attachment snapshot/lean/Sheaf/CategoryTheory/ExtremeBimoduleAttachment.lean
```

Exit status 0. The wrapper compiled `Sheaf/Stage2/Sandbox0.lean` (2.1 seconds)
and `Sheaf/CategoryTheory/ExtremeBimoduleAttachment.lean` (2.2 seconds), with no
diagnostics. The installed wrapper currently invokes the server side-overlay
compiler, which reported a private `/dev/shm/nt-tmp/nt-local-compile-…/.lbuild`
overlay. No global build or live Lean write was run. The unchanged theorem
signature matches the node's `lean.statement` after whitespace normalization.

