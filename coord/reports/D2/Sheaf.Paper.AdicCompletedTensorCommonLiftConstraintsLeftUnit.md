## What changed

Marked `completed_tensor_common_lift_constraints_left_unit` as
`STATEMENT-DISPUTED` without changing its signature or proof hole. Added the fully
proved private diagnostic `left_unit_universal_obstruction` in the item module
and its private Mathlib preadditive-functor-category import. The diagnostic
constructs a second admissible data record by negating only the tensorator. It
proves that the left-unit equation cannot hold for all such records at an object
whose realized identity differs from its negative. This is a precise conditional
refutation in the actual native types, rather than an appeal to a different
category. It does not invoke the disputed theorem or any of its sibling constraint
lemmas. No public declaration, definition, target, or caller changed.

## Proved and sorry left

Proved the private diagnostic `left_unit_universal_obstruction`: assuming a datum
and an object A with `𝟙 (ordinary.obj A) ≠ -𝟙 (ordinary.obj A)`, not every datum
satisfies the asserted left-unit equation at A. Its proof is complete. The
condition on A remains explicit; no concrete native witness for it is claimed
as Lean-certified here. The corresponding mathematical example is a nonzero
coefficient object at a geometric point, over the characteristic-zero coefficient
field.

Closed 0 of the original 1 holes; added 0 holes; split off 0 statements. The sole
remaining sorry is
`WeilConjectures.AdicQbarRealization.completed_tensor_common_lift_constraints_left_unit`,
node `new-sf-adic-completed-tensor-common-lift-constraints-left-unit`. No new
library axiom or hollow definition was introduced. This delivery diagnoses a
false universal statement; it is not counted as proving or decomposing that
statement. The native-context scratch diagnostic compiled in 4.9 seconds;
its axiom audit inherits `sorryAx` from existing native operation definitions.
It is therefore not advertised as a sorry-free certificate for the entire native
construction. The diagnostic proof itself contains no sorry and does not import
the assigned theorem.

## No longer needed

No imports, nodes, or modules are pruned. No new nodes are needed for the private
proved diagnostic. The DAG's existing statement, Lean attachment, dependency
lists, and planned proof remain unchanged; no completed proof route is claimed.
The only new import is a private proof import for negation of natural isomorphisms.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: `CompletedTensorCommonLiftTensorUnit` has exactly two fields,
`tensor` and `unit`, each an arbitrary isomorphism. Neither is related by a field
to the finite models N or to the native coherence. The theorem quantifies over
every such pair, including pairs other than the witness constructed by
`completed_tensor_common_lift_tensor_unit`. The node's sole proof step proposes
representing the selected constraint at a finite field and applying native
coherence. That step does not identify arbitrary `data.tensor` or `data.unit`
with those finite representative maps.

The checked sign test fixes `data.unit` and replaces `data.tensor` by
`-data.tensor` in the preadditive functor category. This remains a natural
isomorphism: both its hom and inverse are negated. No property of N or coherence
is affected because neither hypothesis mentions data. Write a for the fixed
unit tensor identity map, t for the tensorator component, b for the realized
source unitor, and e for the native target unitor. If the universal theorem were
true, it would give both `a ≫ t ≫ b = e.hom` and
`a ≫ (-t) ≫ b = e.hom`. Preadditivity gives `-e.hom = e.hom`.
Precomposing with e.inv gives `𝟙 = -𝟙`. The diagnostic proves these steps in Lean.
For an empty scheme, the zero object, or an object with identity equal to its
negative, this particular contradiction need not apply; its explicit hypothesis
records that limitation. In particular it is not asserted that every nontrivial
monoidal category admits this sign counterexample.

The previously marked finite-agreement component has a related missing-
normalization issue, but it is not imported as a proof. The original theorem
cannot be honestly split into true finite-representative lemmas while retaining
its universal quantifier over these arbitrary data. Adding the desired unit law
as a field or as a repackaged new sorry would merely assume this obligation.
A genuine repair must retain the constructed tensorator and the actual normalized
unit comparison in the construction interface, propagate those equations through
the constraint constructor, and prove the finite coefficient action square for
those maps. That shared-interface repair must also account for the other three
constraint components and the common-lift/coherence callers. Their existing
signatures and sources have been preserved in this delivery.

The local PDFs were read at BS Remark 6.8.15 (printed page 62) and HRS Lemma 7.9
(printed page 22). They discuss the natural operations and finite-coefficient
colimit equivalences; they do not assert the displayed law for every arbitrary
pair of isomorphisms. LeanFinder returned generic tensor/coherence lemmas, and
Loogle returned the monoidal-functor unitality axioms. Those APIs assume unitality;
they do not derive it for unconstrained data. Project and Mathlib searches give
no existing normalization hypothesis for the assigned data type.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsLeftUnit": "cb6ddcc91e866bef84e744dccd357ce7a9574f49"}, "results": {"Sheaf.Paper.AdicCompletedTensorCommonLiftConstraints": {"hash": "0eca76ecbd74c77926bc1ebafe60cb4ed3e413b3", "status": "OK"}}, "seconds": 28, "time": "2026-10-28T10:37:25+0800", "transitive": 0, "version": 1}
```

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
