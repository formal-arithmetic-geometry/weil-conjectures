## What changed

Marked `CategoryTheory.Over.DescentDatum.glued_model_chart_pullback_single` with
`STATEMENT-DISPUTED` and a concrete counterexample. No declaration, signature, import,
or proof was changed. This is a disputed-statement delivery, not a proof or decomposition.
The worker rule in roles/worker.md §2.7 and coord/brief-stage3.md §4 requires this when
an intermediate statement is false. No weaker statement is substituted.

## Proved and sorry left

Holes closed: 0 of 1. Holes added: 0. Split off: 0.

The existing hole remains in
`CategoryTheory.Over.DescentDatum.glued_model_chart_pullback_single`
(node `lem-pd-glued-effective-model-chart-pullback-single`).

For validation only, two sorry-free scratch declarations were compiled:
`chart_pullback_counterexample` and `chart_pullback_singleton_false`.
Both print axioms `[propext, Classical.choice, Quot.sound]`.
The latter refutes precisely the original signature specialized to `p = identity`
and a singleton index. It never invokes the disputed declaration or any project lemma.
These are counterexample experiments, not new library declarations or dependencies.
Their complete source is included below so the independent reader can reproduce them.

## No longer needed

None. No imports removed, no nodes or modules pruned, and no unit route bypassed.
A false statement cannot legitimately be decomposed into true sufficient intermediate lemmas.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: The data in the signature do not imply that the charts are
inverse images of their images in the target. They contain no cover of V and no
information identifying target overlaps with descended source overlaps.

Take any field k and let S = Spec k. Set X = Y = W₀ = S, p = identity,
V = S ⨿ S with V.hom the fold map, I = Unit, U its first component,
W i the identity object S over S, q i the isomorphism from that component to S,
q₀ the fold map, and j i = identity. The hypotheses hold as follows:

| Hypothesis | Verification |
|---|---|
| hcart | Both horizontal maps are isomorphisms and the square commutes. |
| hopen | The identity map is an open immersion. |
| hcover | Its image is all of S. |
| hover | Both sides are identity. |
| hcomm | The fold map restricts to the component isomorphism. |

The conclusion would say the first-component inclusion U.ι is a pullback of
j i = identity. `IsPullback.isIso_snd_of_isIso` then makes U.ι an isomorphism.
It is not surjective: the point in the second component is outside its image.
The scratch proof below implements this argument for every scheme S with a point,
so no particular representation of Spec k is needed.

Even adding a cover of V and hcart for all indices would not repair the statement:
take two indices for the two components and use the same W i = W₀ = S and
j i = identity for both. Then U covers V, but the target identifies the two
disjoint source charts. The source construction in Tag 0AP4 glues along the
*descended overlaps*; arbitrary open immersions satisfying the displayed equations
need not be the result of that construction. Its overlap information was erased
when `exists_glued_model_data` was split from the chart-square verification.
A repair must retain that information through the gluing interface, rather than
assert cartesianity of every possible W₀, q₀, j satisfying these weaker conditions.

The sole proof dependency listed for this node,
`lem-pd-glued-effective-model-charts`, is its ancestor:
GluedEffectiveModelCharts imports GluedEffectiveModelChartsPullback, which imports
this item. The read-only `tools/import_direction.py may` check rejected importing
that module here because it closes a cycle. Thus the one-step DAG plan is both
missing the necessary overlap hypothesis and circular as a Lean proof dependency.
No source or unit record was changed.

Short-route searches were performed with leanfinder, loogle, msearch grep, and rg.
Mathlib has `Scheme.isPullback_of_openCover`, but it requires cartesianity on
actual pullbacks of the cover, which is exactly the missing geometric information.
It cannot prove this false universal statement.

Reproduction: save the following module under a scratchpad lean/ directory and
compile it through `/home/ubuntu/weil-launcher/lcompile.py`. It compiled without
warnings or errors; both axiom checks exclude sorryAx.

```lean
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

/-- Counterexample data for the singleton-index version, for every pointed scheme. -/
theorem chart_pullback_counterexample (S : Scheme.{u}) (x : S) :
    ∃ (V : Over S) (U : V.left.Opens) (q : U.toScheme ⟶ S),
      IsPullback q (U.ι ≫ V.hom) (𝟙 S) (𝟙 S) ∧
      q = U.ι ≫ V.hom ∧
      ¬ IsPullback q U.ι (𝟙 S) V.hom := by
  let a : S ⟶ S ⨿ S := coprod.inl
  let U : (S ⨿ S).Opens := a.opensRange
  let e : S ≅ U.toScheme := IsOpenImmersion.isoOfRangeEq a U.ι U.range_ι.symm
  let f : S ⨿ S ⟶ S := coprod.desc (𝟙 S) (𝟙 S)
  have he : e.inv ≫ a = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  have hq : e.inv = U.ι ≫ f := by
    rw [← he, Category.assoc]
    simp [a, f]
  refine ⟨Over.mk f, U, e.inv, ?_, hq, ?_⟩
  · exact IsPullback.of_horiz_isIso ⟨by simpa using hq⟩
  · intro h
    have : IsIso U.ι := h.isIso_snd_of_isIso
    obtain ⟨z, hz⟩ := U.ι.surjective ((coprod.inr : S ⟶ S ⨿ S) x)
    have hx : (coprod.inr : S ⟶ S ⨿ S) x ∈ (U : Set (S ⨿ S : Scheme.{u})) := by
      rw [← U.range_ι]
      exact ⟨z, hz⟩
    obtain ⟨y, hy⟩ := hx
    exact inl_ne_inr S S y x hy

#print axioms chart_pullback_counterexample

/-- The exact disputed signature, specialized only to p = identity and I = Unit, is false. -/
theorem chart_pullback_singleton_false (S : Scheme.{u}) (x : S) :
    ¬ (∀ (V : Over S) (U : Unit → V.left.Opens) (W : Unit → Over S)
      (q : ∀ i, (U i).toScheme ⟶ (W i).left)
      (W₀ : Over S) (q₀ : V.left ⟶ W₀.left)
      (j : ∀ i, (W i).left ⟶ W₀.left) (i : Unit),
      IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom (𝟙 S) →
      (∀ i, IsOpenImmersion (j i)) →
      (∀ w : W₀.left, ∃ i, ∃ z : (W i).left, j i z = w) →
      (∀ i, j i ≫ W₀.hom = (W i).hom) →
      (∀ i, q i ≫ j i = (U i).ι ≫ q₀) →
      IsPullback (q i) (U i).ι (j i) q₀) := by
  obtain ⟨V, U, q, hcart, hcomm, hnot⟩ := chart_pullback_counterexample S x
  intro H
  apply hnot
  exact H V (fun _ ↦ U) (fun _ ↦ Over.mk (𝟙 S)) (fun _ ↦ q)
    (Over.mk (𝟙 S)) V.hom (fun _ ↦ 𝟙 S) () hcart
    (by intro i; exact inferInstanceAs (IsOpenImmersion (𝟙 S)))
    (by intro w; exact ⟨(), w, by simp⟩)
    (by intro i; simp)
    (by intro i; simpa using hcomm)

#print axioms chart_pullback_singleton_false
```


## Second reading by V1

1. **Interface preservation — pass.** Compared the only delivered module with the
   repository using `diff -u`. The entire difference is the ten-line
   `STATEMENT-DISPUTED` block comment before the existing docstring. All declaration
   signatures, visibility, docstrings, imports, and proof bodies are byte-for-byte
   unchanged. There are no adapted modules, new delivered declarations, definitions,
   or change records. No target statement or meaning was changed.

2. **Compilation and trust — pass for a disputed-statement delivery, not a proof.**
   Independently compiled the delivered module through `lcompile.py` (exit 0), then
   a scratch copy with `#print axioms` for
   `CategoryTheory.Over.DescentDatum.glued_model_chart_pullback_single`.
   It prints `[propext, sorryAx, Classical.choice, Quot.sound]`, as expected for
   its one unchanged, reported hole.
   Independently recompiled the complete counterexample module quoted above (exit 0).
   Both scratch declarations print exactly
   `[propext, Classical.choice, Quot.sound]`. Their imports are exclusively Mathlib;
   the refutation does not depend on the disputed theorem or any project hole.
   There is no forbidden declaration or hollow definition in the delivery.

3. **Split statements and small cases — pass; none split off.** Read both scratch
   proofs top down and checked the specialization against every binder of the
   original signature. The first component of `S ⨿ S` satisfies `hcart` because
   its map to S is an isomorphism; identity j is open and covers W₀; the fold map
   supplies both commutativity equations. Cartesianity would make the component
   inclusion an isomorphism, contradicting disjointness of coproduct components
   at the given point x. Any nonempty scheme, in particular Spec of a field,
   supplies this example. Thus the universally quantified original statement is
   false. The same construction on both components also explains why a source
   cover and cartesianity for all charts alone do not restore it. No scratch
   declarations are part of the delivered library or need new DAG nodes.

4. **Shortest route and pruning — disputed route confirmed.** Independently
   searched `lean/Sheaf` and `lean/WeilConjectures`, and ran msearch grep for
   `isIso_snd_of_isIso|inl_ne_inr|isPullback_of_openCover`. Inspected Mathlib's
   `Scheme.isPullback_of_openCover`: it needs cartesianity on the actual inverse
   images of covering charts, information absent here. No sound shorter proof
   can prove this signature. Read the imports and proofs of
   GluedEffectiveModelCharts and GluedEffectiveModelChartsPullback: importing
   the proposed dependency GluedEffectiveModelCharts into this item closes
   exactly the cycle reported above. No completed proof exists whose dependencies
   could be pruned. Existing public imports are retained for this comment-only
   dispute notification; their minimization belongs with the interface repair.
   `## No longer needed` is complete: nothing removed or bypassed. Read
   `dag/units/sk-prop-jacobian-descent.json`; its route and `realized` are unchanged.

5. **DAG agreement — inherited defect correctly reported.** Read the item's full
   node and the proposed dependency's node against their Lean declarations. No
   node metadata changes are delivered because no proof or statement changed.
   The existing proof plan claims an overlap identification not implied by its
   Lean signature and points to its own importing ancestor. These are defects in
   the inherited plan, not evidence of a successful proof. The dispute comment
   and this report preserve them for the maintainer's coordinated repair; changing
   `proof_deps` to suggest a valid replacement would be misleading. No new nodes
   require field, docstring, search, or statement checks.

Second-reading changes: appended this independent review and reproduced the
compilation, axiom checks, and counterexample. No delivered Lean or node edits.
Verdict: deliver the substantiated disputed-statement notification. Holes closed
0 of 1; holes added 0; split off 0; pruned none. This is not proof progress.
