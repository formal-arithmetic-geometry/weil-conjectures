## What changed

Preserved the original signature and `sorry` of
`CategoryTheory.site_injective_cech_acyclic`, and added a `STATEMENT-DISPUTED` marker
for the independent coefficient/site universes. Removed the proposed new theorem
`site_injective_cech_positive` and its node: it only repackaged the unproved
positive-degree clause, and its statement has the same universe fault.

Retained the genuinely proved new module
`Sheaf.CategoryTheory.SiteCechZeroCohomology`, containing
`CategoryTheory.site_cech_zero_cohomology`. It proves the degree-zero clause for
all abelian sheaves without an injectivity hypothesis. This independent theorem
is delivered for reuse when the disputed item's universe issue is resolved.
It is not imported into the item, whose proof is still open.

## Proved and sorry left

`CategoryTheory.site_cech_zero_cohomology` is proved, with node
`lem-weil-pbc-site-cech-zero-cohomology`. Its private helper `cech_zero_glue` is
proved too. Scratch `#print axioms` checks of both show exactly `propext`,
`Classical.choice`, and `Quot.sound`.

`CategoryTheory.site_injective_cech_acyclic` remains the original named `sorry`,
with node `lem-weil-pbc-site-injective-cech-acyclic`; it is now explicitly
statement-disputed. Its axiom check shows the three permitted axioms plus `sorryAx`. No new `sorry` is added.
Thus zero of the item's one original theorem is closed; one auxiliary public
theorem is proved. This is a dispute delivery, not a completed acyclicity proof.

## No longer needed

No original import or original DAG dependency is pruned. The original node's
`proof`, `proof_deps`, and `proof_origin` are restored unchanged because its proof
remains open. In particular, `def-weil-pbc-sites-and-cohomology`,
`lem-weil-pbc-sheafification-exact`, and `def-weil-pbc-site-cech-complex` stay in
its original plan. The sandbox-only positive-clause theorem and node, and the
item's sandbox-only import of `SiteCechZeroCohomology`, were removed; they are not
pruned nodes of the repository.

## Where the brief, the DAG or earlier work was wrong

The first reader's claimed reduction combined a proved degree-zero clause with
a new `sorry` that merely restated the positive clause. It did not implement the
free-complex/injective-extension argument. The positive node's purported search
records also did not match `searches.jsonl`. Both the theorem and the node are
removed rather than presenting this as a completed proof.

More seriously, the original signature allows `C : Type u`, hom universe `v`,
and coefficients `AddCommGrpCat.{w}` with no size relation. The literature's
free representables and exact sheafification need not belong to this small
coefficient category. The upstream
`CategoryTheory.Sheaf.exactAt_cechComplex_of_injective` in
`WeilConjectures.CategoryTheory.Sites.CechCriterion` instead uses
`AddCommGrpCat.{max w v}` for `C : Type w`, and assumes `HasSheafify`.
The existing module-presheaf cocycle lifting theorem in
`Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechExact` is already marked
with the analogous universe dispute, so it is not a sound workaround.

The source statements were read at Stacks [03AN](https://stacks.math.columbia.edu/tag/03AN),
[03AW](https://stacks.math.columbia.edu/tag/03AW), and
[03F6](https://stacks.math.columbia.edu/tag/03F6).
03AN directly gives the degree-zero identification. 03AW transfers sheaf
injectivity to presheaves by 03F6 and then applies exactness of the free complex.
The size problem is in the formalized signature, not a counterexample to Stacks'
usual appropriately sized categories.

Counterexample in words, including a precoverage satisfying the hypotheses:
work on `Type 1` with small (`Type 0`) coefficient groups. Let `P_A(X)` be `A`
for nonempty `X` and zero for empty `X`; restrictions between nonempty objects
are identities. Every small-valued presheaf on `Type 1` sends parallel maps to
the same homomorphism. Indeed, if maps `f,g : X -> Y` were distinguished, the
evaluations from `P = (Type 0 -> Y)` would give an injection of `Type 0` into the
small set of homomorphisms from `F(Y)` to `F(P)`: for distinct indices `z,z'`,
precompose with the function taking value `f(x)` at `z` and `g(x)` elsewhere.
This contradicts `not_small_type`. Consequently, for injective small `A`,
`P_A` is injective as a small-valued presheaf: evaluate an extension problem at
a one-point object, extend there into `A`, and define the extension at every
nonempty object by restriction to a chosen point. Independence of the point
and naturality follow from the parallel-map equality; at the empty object the
extension is zero. Monomorphisms of presheaves are componentwise monomorphisms.
Take `A = Q`, which is injective as an abelian group.

Use the precoverage whose covering families are jointly surjective on pairs:
for every ordered pair of points of the target, one family member has lifts of
both points. This condition is stable under isomorphisms, composition, and base
change. Types have the required pullbacks. Empty covers of the empty object are
allowed. `P_Q` is a sheaf for this precoverage: for nonempty target, choose one
point in each nonempty covering object. The pair-lifting condition and the
compatibility condition compare any two such sections via a third covering
object and one-point test objects. Thus they all equal one element of `Q`,
which is the unique amalgamation. If the target is empty, every section is zero.
The equivalence between the precoverage and generated-topology sheaf conditions
then makes this a sheaf for `J.toGrothendieck`. Injectivity of the presheaf implies
injectivity of this sheaf, since the inclusion preserves monomorphisms.

Now cover the three-point object by its three two-point subsets (the edges of a
triangle), regarded as large types by lifting. Every pair of vertices belongs
to one edge, so this is a covering. Pairwise edge intersections are nonempty;
the intersection of all three distinct edges is empty. A degree-one cochain
assigning 1 to the oriented pair `(0,1)`, -1 to `(1,0)`, and zero to the other
pairs is a cocycle: triples with repetition cancel, and triples with all three
distinct indices take values in the zero group. It is not a coboundary: the
sum around `(0,1),(1,2),(2,0)` is 1, whereas any coboundary has sum
`(b1-b0)+(b2-b1)+(b0-b2)=0`. Thus its first Cech cohomology is nonzero.

The complete site and cochain counterexample above is a mathematical argument,
not a kernel-certified refutation of the original theorem. The scratch file
`Collapse.lean` does certify the parallel-map collapse, injectivity of `P_A`,
injectivity inherited by a sheaf from an injective presheaf, and the numerical
cyclic obstruction. It compiles with no errors; its three printed axioms lists
use only the permitted axioms. Scratch files are not delivered.

## New nodes

`lem-weil-pbc-site-cech-zero-cohomology` records the independent, proved
identification from Stacks 03AN. Its proof first derives compatibility from the
zero differential using the specified product universal property, then applies
the sheaf condition and identifies degree-zero abstract homology with the
concrete kernel. The recorded searches correspond to actual entries in
`searches.jsonl`, including the unavailable LeanSearch service. No new node with
`sorry` survives this reading. No change record is needed because no existing
statement, definition, or public import is changed.

## Second reading by E2

1. Compared the item with the repository by `diff`. Its existing declaration
   signature is byte-for-byte identical; its body is the original `by sorry`.
   Only the dispute comments are added. The other delivered module is new and
   defines no replacement notion. The original node is byte-for-byte restored.
   No change to an existing public interface is being delivered.
2. Compiled both modules locally in import order. Inspected every declaration:
   no `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, no hollow
   definitions, and no new `sorry`. Scratch copies print the axioms of the
   private gluing helper, public degree-zero theorem, and original theorem:
   the first two use exactly the permitted three axioms; the last uses
   `sorryAx`, as expected for the explicitly open theorem.
3. Refused and removed the positive-clause split, for both relabelling and the
   mathematical size issue above. The retained zero-degree theorem is true for
   empty covers (the sheaf axiom forces sections on the covered object to be
   zero), singleton covers, and arbitrary product choices. Checked its finite
   index transports: `Fin 1` families are constant, the two differential terms
   give equality of restrictions, and the universal-property map handles
   arbitrary equal-composite test arrows. Its unique amalgamation supplies
   both injectivity and surjectivity of restriction. No injectivity assumption
   is used. Read 03AN against this argument. Its node and docstring give the
   whole proof. Additional independent searches used LeanFinder with
   'Zeroth cohomology of a sheaf Cech complex is the kernel equalizer of
   restriction maps' and Loogle with '"homology", "IsZero"'; neither gives
   this theorem. Searched `lean/Sheaf` and `lean/WeilConjectures` for
   `SiteCechComplex`, `cech_zero_cohomology`, and alternate Cech terminology.
   Upstream exactness and sheaf-gluing lemmas are ingredients, not the same
   degree-zero statement for this chosen complex.
4. Reviewed the proof from the target downward. It cannot be closed faithfully
   by the proposed positive helper. Kept the valid zero-degree proof and the
   original open route, rather than treating an unproved clause as progress.
   Every import of the new module serves its statement or proof, and the
   homology-in-abelian-groups import is plain `import`. There are no unused
   new imports in the item. `## No longer needed` accounts for all three old
   proof dependencies: none is pruned. Read `dag/units/sk-thm-p1.json` and its
   `realized` entries; this auxiliary node is not a unit step replacement,
   and no entry or unit route is changed.
5. The existing item's proof plan, dependencies, and origin are unchanged,
   reflecting that its proof remains open. The new zero-degree node follows
   the code's compatibility/gluing and kernel-isomorphism steps; its dependency
   list is their union, its declaration record matches its signature, and it
   has the required source, searches, creation, blueprint, chapter, and unit
   fields. The private helper has a complete proof and adds no open obligation.

Changes made in this reading: removed the false/relabelled positive helper and
its node; restored the original item's proof and node; removed its unused new
import; added the explicit universe dispute and the detailed counterexample;
corrected the report's proof and pruning claims. The sound degree-zero proof
was retained without rewriting it.
