## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.PerfectDerivedTensorHom`, declaration
`AlgebraicGeometry.exists_perfectDerivedTensorHomEquiv`, with a specialization of
`AlgebraicGeometry.scheme_derivedInternalHom_adjunction`. Destructure the existing
adjunction to obtain its symmetric equivalence `e` and symmetric naturality `hn`.
Use `fun A I _ _ E ↦ e I A E` as the requested equivalence family. Its naturality is
exactly `hn I I' A A' E E' g f h t`; perfectness is retained in the signature but is
not required by the general adjunction. No signature, docstring, import, definition,
visibility, or other module changed.

The single-file compile through lcompile.py succeeded without errors or warnings.
Lean Finder found ordinary sheaf/condensed tensor-Hom results, rather than this
scheme-derived statement. Library search found the existing general adjunction and
other specializations of it. The source node's route is already the shortest route.

## Proved and sorry left

Closed one local hole:
`AlgebraicGeometry.exists_perfectDerivedTensorHomEquiv`
(node `lem-sc-affine-perfect-derived-tensor-hom`). No sorry remains in the item.
No holes added or split off. This is a complete proof from the already stated
adjunction, not a decomposition into new statements. It still depends on the
adjunction's existing transitive unfinished theory; no claim of an entirely
sorry-free dependency closure is made.

## No longer needed

None. The proof needs the existing proof import
`Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction`, and the three public imports
provide the perfectness, derived tensor, and derived internal-Hom interfaces used by
the unchanged statement. No node or module in the planned route is bypassed.
The node's proof, proof_deps, and proof_origin already describe exactly this
specialization, so no node copy or route update is needed. The unit record
`sk-thm-picard-duality` is unchanged.

## Where the brief, the DAG or earlier work was wrong

None. The site expressions written using `X` and `X.toRingedSpace` are definitionally
compatible, as verified by the successful compile. The symmetric naturality swaps
both the objects and their precomposition morphisms: use `g` for the K-variable
and `f` for the L-variable to obtain the required tensor map `f ⊗ₘ g`.

## Second reading by T2

1. PASS: compared the sole delivered module with the repository using `diff -u`.
   Only `by sorry` became a four-line proof. The existing signature, docstring,
   imports, visibility, and surrounding text are byte-for-byte unchanged; there
   are no definitions, additional modules, nodes, or change records in this delivery.
2. PASS: independently compiled the delivered file through lcompile.py, with no
   errors or warnings. A scratch copy with `#print axioms
   AlgebraicGeometry.exists_perfectDerivedTensorHomEquiv` compiled and reported
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter
   belongs to the existing imported unfinished theory. The delivered source has
   no sorry or prohibited declaration and constructs no data from existence.
   Destructuring the adjunction happens inside a theorem proving an existential.
3. PASS: no statements were split off or added, so there are no new holes or
   small-case obligations. Checked the specialization with K=I, L=A, M=E:
   its symmetric tensor order is A tensor I and its naturality takes a=g, b=f,
   c=h. Thus it gives exactly f tensor g on the right, including identity and
   zero morphism cases. Independently searched Mathlib using
   `tensor.*homEquiv|homEquiv.*tensor|tensorHomAdjunction` and searched lean/ for
   this adjunction and its perfect specializations. The Mathlib hits concern
   ordinary modules or representations; the existing scheme adjunction is the
   direct applicable result. No duplicate helper is needed.
4. PASS: the proof takes the existing general symmetric adjunction directly.
   PerfectComplex supplies the perfectness predicates, DerivedTensorStructure
   supplies the tensor structure, and DerivedInternalHom supplies RHom in the
   signature. The adjunction is correctly a plain proof-only import. The single
   old proof dependency is used, so `## No longer needed` is complete. Checked
   the unit sk-thm-picard-duality and its realized fields; no route is bypassed
   or modified.
5. PASS: read lem-sc-affine-perfect-derived-tensor-hom and its adjunction
   dependency. The node's proof explicitly says K=I, L=A, M=E in the symmetric
   form, its sole proof_deps entry is the theorem used, and its document-based
   proof_origin matches the route. No node update is necessary.

Second reading changed only this report by adding the independent review.
No Lean repair was needed. Closed 1 local hole, added 0, split off 0, pruned none;
the pre-existing dependency closure still contains unfinished proofs.
