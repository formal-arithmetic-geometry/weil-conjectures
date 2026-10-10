Files written:

- `dag/nodes/sec-abelian-varieties/def-sp-homological-functor.json`: existing item updated; kind definition, Mathlib verdict `CategoryTheory.Functor.IsHomological` at `Mathlib/CategoryTheory/Triangulated/HomologicalFunctor.lean:82`.
- No new nodes.

Attachments:

- None: no sorry-free project declaration carries the blueprint tag.

WANTED:

- None.

What was wrong or incomplete:

- The imported item had no Mathlib search record and was marked `imported`. The definition is already supplied by Mathlib's `CategoryTheory.Functor.IsHomological`; the item is therefore a Mathlib leaf. The Mathlib class states preservation of zero morphisms and exactness of the image short complex of every distinguished triangle, and the surrounding Mathlib file supplies additivity for such functors.
- The unit record attached to this imported definition is unrelated to the proper-and-quasi-finite proposition; this worker did not alter the unit because the brief permits only realized-field changes for a key node and this item is not that unit's statement.

What could not be finished:

- Nothing.

## Review by J1

I read the item JSON, its chapter record, the source repository's triangulated homological-functor files, and the Mathlib definition at `Mathlib/CategoryTheory/Triangulated/HomologicalFunctor.lean:70-88`. The source has no declaration tagged `(blueprint: def-sp-homological-functor)`, so there is no project attachment. The Mathlib class `CategoryTheory.Functor.IsHomological` introduces the same pretriangulated-to-abelian homological-functor notion by requiring exactness of the mapped distinguished-triangle short complex; its `PreservesZeroMorphisms` field and the file's additivity instance account for the additive requirement in the imported prose. I searched the whole DAG and blueprint and found no duplicate definition node. I ran two LeanFinder searches, two Loogle searches, two Mathlib grep searches plus a second grep phrasing, and LeanSearch; the latter was unavailable and is recorded as such. Because this is a Mathlib leaf, it has no proof steps and `citations.json` is empty. The node now records the Mathlib declaration, source line, search results, and `status: mathlib`.

## Second reading by J1

- Item statement: checked clause by clause against the imported blueprint definition and Mathlib's `CategoryTheory.Functor.IsHomological`; the pretriangulated/abelian hypotheses, distinguished-triangle exactness, and additivity are present (the latter via the file's instance at line 153). Verdict: correct.
- New node `def-sp-homological-functor`: no separate node; the item itself is the sole Mathlib leaf, with statement only, `def-sp-abelian` dependency, exact declaration/file/line audit, and recorded searches. Verdict: correct.
- Proof steps: none, since this is a Mathlib leaf; `citations.json` is correctly empty.
- Small cases: zero objects and the zero functor satisfy mapped exactness; a field target is covered by the abelian-category hypothesis; no scheme or numerical parameter occurs. Verdict: passed.
- Changes made: set `blueprint.same_as` to the searched empty list and expanded `mathlib_match.how` to cite both the class declaration (line 82) and additive instance (line 153), closing the additivity audit gap.
