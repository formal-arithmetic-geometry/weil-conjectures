## What changed

Replaced the sole `sorry` in `AlgebraicGeometry.sheafHom_restrictScalars_counit` by
an explicit construction of `Adjunction.CoreHomEquiv`. Private helpers construct
evaluation at one and the transpose on local internal-Hom sections, transport the
transpose through the supplied natural isomorphism, prove linearity and restriction
compatibility, establish both inverse laws, and verify naturality in both arguments.
The helpers work over arbitrary sheaves of commutative rings; the final proof
specializes them to the scheme morphism. All definitions are actual constructions.

The original public theorem statement, visibility and three public imports are
unchanged. The implemented route is the node's existing evaluation/transpose plan;
no DAG update, exported interface change, forced adaptation or new node is needed.
The conservative static command check requires the change record
`coord/changes/sheaf-coinduction-counit-private-construction.md`, documenting the
section-scoped variables, notation and local instance registration.

## Proved and sorry left

Closed: `AlgebraicGeometry.sheafHom_restrictScalars_counit`
(node `lem-sc-sheaf-coinduction-counit`), one of one original holes.
Added holes: none. Remaining holes in this delivery: none.
All private helper lemmas and all proof fields of private definitions are proved.
The delivery is a proof, not a decomposition into unproved intermediate statements.

## No longer needed

None. No import, module or planned proof dependency is pruned. The three existing
public imports supply the scheme, restriction-of-scalars and internal-Hom notions
used by the unchanged public signature. `def-pur-sheaf-hom` remains used, and no
other Sheaf statement module is imported.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had a complete-looking proof but did not pass the 60-second
compile limit. Replaced broad `ext` calls with explicit `ModuleCat.hom_ext` and
`LinearMap.ext` applications; the complete module then compiled in 52.6 seconds.
The public theorem signature was checked textually against the repository and is
identical. There are no lines longer than 100 characters.

No mathematical statement or planned step required correction. The larger ring's
commutativity is inherited from its commutative-ring sheaf. Implementing the
construction generically over ring sheaves avoids expensive kernel reductions of
the scheme pushforward; this changes only private proof machinery and preserves
the node's argument. The construction works for empty opens and zero rings and
uses no nonemptiness or nonzero-ring hypothesis.

The static interface detector treats even section-scoped helper commands as
interface changes. The required change record explains their scope; no downstream
signature or proof is changed, and the commutativity structure is registered as an instance locally.

## Second reading by U2

1. Compared the delivered module with the repository version. The public theorem statement and all existing declaration signatures are byte-for-byte unchanged; only private proof construction and the theorem proof changed.

2. Compiled the delivered module with `lcompile.py` (53.5 seconds) and checked the axiom probe: the public theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations.

3. Searched Mathlib and the library for an existing sheaf coinduction/internal-Hom adjunction. No declaration gives this varying-sheaf-of-rings result; the explicit construction is therefore needed. No new statement or node was added, and the existing node remains exactly the theorem proved.

4. Reviewed the proof from the target downward. The transpose/evaluation maps, inverse laws, and both naturality laws implement the node's stated route. The unit route is unchanged; no imports or proof dependencies can be pruned.

5. Checked the DAG node against the Lean proof and report. The node's statement, proof origin, and dependency remain correct; no split-off holes or hollow definitions were introduced. The local commutative-ring instance is scoped to the private construction section.

Changed during second reading: restored the scoped helper to a `private instance` (matching its intended use and change record), updated the change record wording, and added this review section.
