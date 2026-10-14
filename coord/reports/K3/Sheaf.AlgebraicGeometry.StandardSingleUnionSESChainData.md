## What changed

Replaced the original hole in `Sheaf.AlgebraicGeometry.StandardSingleUnionSESChainData`
by a complete proof from the resolved geometric homotopy comparison and a fully proved,
generic cylinder rectification theorem. The original declaration, its signature and its
docstring are unchanged. Its only additional imports are private proof imports of
`Sheaf.AlgebraicGeometry.StandardSingleUnionHomotopyChainData` and
`Sheaf.CategoryTheory.DerivedCategory.HomotopySquareRectification`.

The rectification proof explicitly constructs T = D ⊞ Cone(id C), the inclusion
(t,inr(id C)) and the corrected map (beta,k), where k is Cone.desc of -h and
alpha t' - t beta. It proves the strict-square equation, constructs the localized
middle isomorphism using contractibility, proves the cone projection invertible by
its distinguished-triangle morphism, and writes the actual homotopy identifying the
strict cone map with the originally specified mapOfHomotopy H. Nothing is chosen from
an unproved mere-existence theorem to define data. All these constructions are private
helpers with complete proofs. The main proof composes the two source isomorphisms and
transports the equations by associativity, retaining the first and all target terms.

The geometric comparison remains a separately named public theorem, before any
strictification. Its module retains the original plan's K-injective resolution,
Mayer–Vietoris presentation, underived open counit-square and direct-image composition
imports for its next worker. The old node now records the two actual proof steps.

Validation: all three delivered modules compiled individually in dependency order
through `lcompile.py`, and `deliver3.py --no-push` printed OK. Its declaration probes
and preflight passed; the second-reading section is intentionally left to the reader.
The original main signature was also compared byte for byte with the repository
signature. No file was pushed.

## Proved and sorry left

Closed the original direct hole in
`AlgebraicGeometry.standardSingle_union_ses_chain_data`
(node `new-pc-standard-single-union-ses-chain-data`). This is a decomposition of the
geometric comparison and a completed proof of the cylinder part, not a claim that the
whole geometric theorem is now independent of sorry.

Added one direct hole:
`AlgebraicGeometry.standardSingle_union_homotopy_chain_data`
(node `lem-pc-standard-single-union-homotopy-chain-data`), whose entire proof is
`:= by sorry` in its own module. Its docstring gives the source and the geometric
construction, and its node keeps all original geometric proof dependencies.

Fully proved, without any direct or inherited sorry:
`CochainComplex.homotopy_square_cone_rectification`
(node `lem-pc-homotopy-square-cone-rectification`). All private helpers are proved.
There are no other holes in the delivered files. Holes closed: 1; holes added: 1;
net direct-hole change: 0. The generic rectification is completed mathematical work.

Edge cases: the generic construction is proved uniformly for every complex and every
specified H, including nonzero homotopies; it uses no flatness, boundedness or geometric
hypotheses. In particular it handles zero complexes and H = 0. The geometric statement
keeps unrestricted coefficients; empty covers give zero rows, and repeated or contained
opens give split rows, so no nonemptiness or disjointness hypothesis has been inserted.

## No longer needed

No module is pruned from the target import closure. All seven old direct proof dependencies
have moved below the new homotopy-comparison node rather than disappeared:
`prop-pur-kinjective-resolutions-exist`, `lem-pc-kinjective-mayer-vietoris-presentation`,
`def-pc-derived-pullback`, `lem-pc-mayer-vietoris-underived-open-counit-square`,
`lem-pc-derived-direct-image-composition`, `def-pc-standard-single-base-change-map`,
and `def-pc-module-pullback`. The original module had only its statement import of
StandardSingleBaseChangeMap; that public import remains. The new geometric module keeps
its private plan imports while its geometric theorem remains open. Generic ConeDiagramSESPresentation and
MappingCylinderSplitFactorization were inspected but are not imported: their statements
respectively start with an already strict square and lack the specified cone-map equation.
They were not original proof dependencies, so this is not counted as pruning them from
the target closure. The new generic rectification imports only Mathlib.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox contained an auxiliary theorem with exactly the original conclusion
and no docstring or node. It has been removed. Such an alias would merely move the hole.
The absence of a complete existing geometric comparison did not justify ABANDON: the
cylinder part can be proved directly from Mathlib while leaving the genuinely geometric
homotopy comparison as the next item. Our new geometric theorem asserts a specified
homotopy square, not a strict square or a replacement complex; the explicit cylinder
construction and its cone homotopy are necessary to recover the original statement.

The unit `sk-thm-picard-coherence` and its route are unchanged. Blueprint searches for
homotopy square and cover comparison found no matching blueprint node. LeanSearch was
unavailable; LeanFinder, Loogle and source searches supplied the generic mapping-cone
APIs. The official source pages for the cited Stacks tags were read during this attempt.
No definition, existing signature, target or module held by another group was changed.

## New nodes

`lem-pc-standard-single-union-homotopy-chain-data`:
`Sheaf.AlgebraicGeometry.StandardSingleUnionHomotopyChainData`, declaration
`AlgebraicGeometry.standardSingle_union_homotopy_chain_data`. This isolates the
resolved-cover comparison and its specified homotopy, before the cylinder replacement.
It retains the original geometric construction and its proof dependencies.

`lem-pc-homotopy-square-cone-rectification`:
`Sheaf.CategoryTheory.DerivedCategory.HomotopySquareRectification`, declaration
`CochainComplex.homotopy_square_cone_rectification`. This generic tool is fully proved
from Mathlib by the explicit cylinder, cone-triangle and homotopy computations above.
Both nodes inherit the item's chapter and unit and identify their place in its proof.
There are no change records or forced adaptations.


## Second reading by K3

1. **Visible interface: PASS.** Read the repository/sandbox diff of the original module.
   Its sole existing public theorem signature is byte-for-byte identical, checked by
   extracting the text from `theorem` through the type before `:= by`. Its docstring,
   universe and public statement import are unchanged. The two additions to its imports
   are private proof imports. The other two modules are new, not adaptations; no change
   record is needed. Compared the existing node as JSON: only `proof`, `proof_deps` and
   `proof_origin` change. No repository file was written and no git command was run there.

2. **Proof and axioms: PASS, with one documented geometric hole.** Independently compiled
   all three modules in dependency order with `lcompile.py --all`: no errors or warnings.
   Read every private cylinder helper: all data are explicitly constructed from t and H;
   the localized inverse is supplied by proved isomorphism data, not an unproved existence
   choice. The strict-square equation, contractible-summand projection, cone-triangle
   isomorphism and explicit cone homotopy are proved. A scratch module importing the three
   delivered modules printed axioms for each public theorem. Rectification uses exactly
   propext, Classical.choice and Quot.sound; the two geometric declarations additionally
   use sorryAx. Text search found exactly the reported public geometric `:= by sorry`,
   no other hole and none of the forbidden declaration mechanisms. Removed the scratch
   probe after compiling it. Hole accounting remains one closed and one added, net zero:
   a decomposition, with the generic cylinder argument fully proved.

3. **Split statement and searches: PASS.** The new geometric statement drops the strict
   equality in favor of a specified homotopy and retains the induced cone map, so the
   proved rectification performs a real additional construction; the item is not proved
   by an alias with its original conclusion. It has a source, natural-language geometric
   proof and matching node. Read the official Stacks pages for 08BV, 08HZ, 08FE, 08HY,
   0DJ9, 013N, 013O and 014P. Here 0DJ9 supplies the induction-diagram motivation, not a
   claim that its quasi-coherence hypotheses hold for arbitrary N. The unrestricted
   construction uses the ringed-space Mayer-Vietoris rows and counit comparison instead.
   Checked empty covers, one empty open, repeated/contained opens and zero coefficients:
   the zero or split rows introduce no extra hypothesis. For the generic theorem the
   kernel-checked argument applies to arbitrary H, including H = 0, and zero complexes.
   Fresh msearch LeanFinder query on lifting derived cover diagrams returned eight
   generic cone APIs; Loogle on mappingCone.descHomotopy returned its constructor; grep
   on cone rectification and union homotopies returned no duplicate. Also searched both
   local Lean roots and read CommutativeSquareLift, EndpointConePresentation and
   ConeDiagramSESPresentation. The first does not prescribe the cone component, the
   second does not prescribe the middle component, and the third assumes a strict square.
   None closes the specified geometric comparison in a few minutes.

4. **Route, imports and pruning: PASS.** The main theorem first obtains the geometric
   homotopy comparison, then uses the fully proved Mathlib-only generic construction,
   then transports the two equations by associativity. No needless new public proof
   imports are present. Read sk-thm-picard-coherence.json: its realized statement/step
   arrays are empty and untouched; this delivery remains within its existing geometric
   route and changes no unit. No closure pruning is claimed. Clarified above that all
   seven original direct proof dependencies move below the geometric node, with their
   names explicitly listed; they are retained in the import closure.

5. **Nodes: PASS.** Both new nodes have source/proof/search/creation/blueprint/chapter/unit
   and Lean fields. Extracted both new theorem signatures and compared them exactly
   with their node lean.statement strings. The main node records precisely the two
   invoked theorems; the geometric node retains the seven original geometric dependencies;
   the generic node records the explicit cylinder, triangle and cone-homotopy calculations
   and has no Sheaf proof dependency. Its statement matches the first and cone terms
   actually preserved in Lean.

Second-reading changes: clarified the direct-dependency versus closure-pruning accounting
under No longer needed and appended this independent review. No Lean proof, signature,
definition, import or node required repair.
