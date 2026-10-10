Files written:

- item: lem-sc-graded-localization-exact, statement node, split; no Mathlib leaf.

Attachments:

- None.

WANTED:

- None.

The imported node had no proof steps. I checked the exact statement against Stacks tag 09MR, label coherent-lemma-invert-s-cohomology, and retained its self-contained graded localization formulation. The proof is split into ordinary exactness after localization and the degree-zero homogeneous-component argument. The existing node lem-weil-pbc-localization-module-exact already states the ordinary localization exactness, so I did not create a duplicate node.

Nothing remains unfinished.

## Review by J1

I read the item source in /home/ubuntu/c1-stacks-review/coherent.tex at the proof paragraph for Lemma 09MR (the checked-out project’s local copy of the Stacks source), and checked the tag label in its tags table. The node’s hypotheses introduce the graded ring, graded modules, homogeneous element, localization grading, degree-preserving maps, and exact sequence explicitly; the localization notion is the cited definition node def-weil-pbc-module-localization-away.

Step 1 cites lem-weil-pbc-localization-module-exact. Its statement explicitly says that an exact sequence of modules remains exact after localization at a multiplicative subset, which is exactly the fact used after forgetting the grading and taking the powers of s. This is the only non-elementary dependency and is declared as a generic tool use because it belongs to another unit.

Step 2 uses only the definitions in the item: localization at a homogeneous element has a direct-sum grading, and degree-preserving maps commute with taking homogeneous components. I checked both directions of exactness: a zero image lifts by Step 1 and the degree-zero component of the lift maps to the given degree-zero element; the reverse inclusion follows from composition being zero. The same component argument works in every degree and hence termwise for finite or infinite exact sequences.

I searched the DAG and blueprint for an existing graded-localization exactness node and found no duplicate. The item’s existing Mathlib searches were retained; fresh searches were run through LeanFinder, Loogle, grep, and LeanSearch, with LeanSearch recorded as unavailable by the search service. No new statement was created, so there were no new-node searches or source hypotheses to test. Small cases checked: s of degree 0 gives the usual degree-preserving localization, and the zero exact sequence remains exact in both localized and degree-zero parts.
