## What changed

Replaced the sorry in `CategoryTheory.Functor.rhom_hom_derived_roof_shift` by a
complete Lean reduction to the shift equation for one explicitly constructed
cocycle on the shift of a bounded below injective complex. The main module proves
existence of injective representatives, surjectivity of the cocycle-to-derived
cohomology composite, and transport using naturality of psi, derived shift,
homology shift, inclusion shift, and shift addition. The existing signature is
unchanged. The original unit route is unchanged.
The forced adaptation of RHomDerivedConnecting adds only the proof import it
previously obtained through the item's public roof import.

Added `Sheaf.CategoryTheory.Abelian.RHomDerivedRoofShiftInjective`, containing the
single-cocycle calculation. Both modules import the definitions they actually
use instead of importing the existential roof-comparison theorem. A local
unused-variable linter option preserves the original names of nondependent
forall hypotheses; no elaboration or kernel checks are disabled.

## Proved and sorry left

Closed `CategoryTheory.Functor.rhom_hom_derived_roof_shift`
(node `lem-sc-p1-rhom-hom-derived-roof-shift`), by a decomposition, not an
axiom-free proof of the full mathematical result. The item's module has no sorry.

Added exactly one remaining hole:
`CategoryTheory.Functor.rhom_hom_derived_roof_shift_injective_cocycle`
(node `lem-sc-p1-rhom-hom-derived-roof-shift-injective-cocycle`). It concerns only
a class explicitly constructed from one cocycle on an injective complex. All
passage to arbitrary cohomology classes and arbitrary derived objects is proved
in the parent. No other sorry or definition was added or changed. One parent hole is closed
and one child hole is added: the net hole reduction from this decomposition is
zero; no whole-library progress figure is claimed.
RHomDerivedConnecting retains its existing proof and has no sorry.

Both modules compile without warnings through lcompile.py --all. The imported
roof existence theorem is not used, even as a sorry dependency.

## No longer needed

Removed `public import Sheaf.CategoryTheory.Abelian.RHomDerivedRoof`.
The proof does not need node `lem-sc-p1-rhom-hom-derived-roof` or its declaration
`CategoryTheory.Functor.exists_rhom_hom_derived_roof`: that theorem asserts
existence of a roof-normalized comparison, whereas this item already assumes
such a comparison and proves its shift equation. The node remains a statement dependency
describing that assumption. Other consumers may still require this module, so
this is pruning of this item's proof dependency, not a claim that the whole
project no longer reaches it.

Also removed `def-sp-kinjective-bridge` from the parent
`proof_deps`: its definitions occur in the unchanged signature, but the parent
proof does not invoke its declarations. Its public import remains necessary,
and the new cocycle node still cites it. This does not prune the bridge module
from the import closure. The remaining required definition and shift nodes stay. No unit statement or realized
unit step was bypassed. No other modules or nodes are pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The original DAG listed the existence theorem for a roof comparison as a proof
dependency although it establishes existence of a roof-normalized comparison
and this item instead receives that comparison as a hypothesis. No invocation of that existence theorem is needed.

The local compiled library initially lacked RHomDerivedRoof. A temporary
unchanged sandbox copy compiled, and was removed after pruning that import.
No missing compiled dependency remains in the delivered set.

The local referenced literature/stacks-project/derived.tex is absent on this
machine. The cited source statements were read at the official Stacks pages:
https://stacks.math.columbia.edu/tag/06XR,
https://stacks.math.columbia.edu/tag/070I, and
https://stacks.math.columbia.edu/tag/05TE. They supply the injective model and
derived-functor framework; the detailed coherence calculation is the original
parent node's expansion, restated precisely in the new docstring.

Edge-case review: the new assertion quantifies over all integers, including
negative degrees; no nonnegative-degree restriction is introduced. It keeps
naturality along the canonical quotient shift isomorphism, which cannot be
omitted for an arbitrary chosen localization. Zero complexes and zero cocycles
are compatible with the additive equations. All objects and maps in the class
construction are explicit; no data is chosen from an unproved existence theorem.

## New nodes

`lem-sc-p1-rhom-hom-derived-roof-shift-injective-cocycle` isolates the original
first proof step's termwise shift calculation for a single cocycle. Its statement
records the canonical shift comparison explicitly and its docstring gives the
complete identity-resolution argument. It is strictly smaller than the parent:
it neither asserts surjectivity onto cohomology nor treats arbitrary derived
objects. LeanSearch was unavailable; LeanFinder, Loogle and source grep are
recorded in the node. Change record: `coord/changes/RHomDerivedRoofShiftImports.md`.

## Forced adaptations

`Sheaf.CategoryTheory.Abelian.RHomDerivedConnecting` (unclaimed) is the only
adapted module. The original compiled against the changed dependency fails:

```
RHomDerivedConnecting.lean:105:29: error(lean.unknownIdentifier):
Unknown identifier `exists_rhom_hom_derived_roof`
RHomDerivedConnecting.lean:105:9: error: Tactic `rcases` failed:
`x✝ : ?m.702` is not an inductive datatype
```

Added exactly one line, `import Sheaf.CategoryTheory.Abelian.RHomDerivedRoof`,
before the existing import of RHomDerivedRoofShift. This restores the theorem
used at line 105 without modifying any declaration, proof, or public import.
The adapted file compiles without warnings. The import change record names
its holder and explains necessity. The independent reader should compare the
original and adapted files against the changed dependency.

## Second reading by G1

1. **Interfaces: PASS.** Compared all delivered existing modules with the repository
   using diff and the declaration parser. The parent's signature is byte for byte
   unchanged. Connecting changes only its one proof import; its signatures,
   visibility, definitions and proof are unchanged. The public import replacement
   is declared in `coord/changes/RHomDerivedRoofShiftImports.md`. No targets or
   mathematical definitions change.
2. **Proof and axioms: PASS as a decomposition.** Independently compiled the three
   delivered modules in import order using lcompile.py: no errors or warnings.
   Scanned the delivered code: exactly one sorry, the named new cocycle theorem;
   no forbidden declarations and no definition added. Scratch copies with
   `#print axioms` for the parent, child and connecting theorem report only
   propext, Classical.choice, Quot.sound and sorryAx. Independently compiled the
   original Connecting against the sandbox overlay: it fails at line 105 with
   unknown `exists_rhom_hom_derived_roof`. The adapted file succeeds, confirming
   the necessity of the single added import. The injective representative and
   cycle witnesses are eliminated within a theorem proof, not used to define
   arbitrary data from an unproved existence claim.
3. **New statement: PASS.** The sole split-off theorem handles one explicit
   cocycle on I[1], not arbitrary derived objects or arbitrary cohomology classes.
   The parent really proves the cycle-surjectivity and isomorphism-transport
   steps. Checked the concrete class, quotient shift isomorphism, units and map
   directions against their definitions. Checked all integer degrees, including
   negative degrees, zero cocycles and zero complexes; no positivity restriction
   or sign correction is missing. Right-target shifting and equivHomShift are
   unsigned, unlike source-shift operations. The complete identity-resolution
   proof in the child's docstring is mathematically valid. Independently searched
   LeanFinder for "cochain cocycle localization target shift addition compatibility
   Hom cohomology", Loogle for Cocycle.equivHomShift, and source grep for cocycle,
   homology, derived unit and shift combinations. Found component lemmas but no
   existing theorem of this type. The remaining coherence calculation is not a
   few-minute closure; no additional holes were introduced. Verified the cited
   official Stacks tags 06XR, 070I and 05TE as framework references, with the
   detailed coherence argument explicitly attributed to an agent expansion.
4. **Route and pruning: PASS after report correction.** The proof follows the
   original injective-representative, cocycle, then naturality route. The unit
   record `dag/units/sk-thm-picard-duality.json` has empty realized slots; neither
   those slots nor any unit/chapter route changes. Every direct import supplies
   declarations or instances appearing in the public signature except the new
   private proof import. No extra theorem-existence import is needed. Compared
   the old and new proof_deps: roof-existence and the bridge are the only entries
   removed. Corrected the report to distinguish removal of the bridge as a
   direct parent proof dependency from retention of its signature import and
   its use by the child.
5. **Nodes: PASS.** Parent changes only proof, proof_deps and proof_origin. Both
   nodes' proof_deps are exactly the unions of their steps' uses. The new node has
   the full source, search, creation, blueprint, chapter/unit and Lean records;
   its Lean statement matches its actual signature. Parent steps describe the
   implemented surjectivity and naturality proof, and cite the sole new hole.

Second-reading changes: corrected the description of the roof-existence theorem,
completed the No longer needed accounting for def-sp-kinjective-bridge, explicitly
recorded zero net hole reduction, and appended this review. No Lean proof,
statement, definition, import or node needed repair.

## Forced adaptations

### Sheaf.CategoryTheory.Abelian.RHomDerivedConnecting
Original against changed dependencies failed:
```
/tmp/forced-adaptation-pfflzpem/lean/Sheaf/CategoryTheory/Abelian/RHomDerivedConnecting.lean:105:29: error(lean.unknownIdentifier): Unknown identifier `exists_rhom_hom_derived_roof`
/tmp/forced-adaptation-pfflzpem/lean/Sheaf/CategoryTheory/Abelian/RHomDerivedConnecting.lean:105:9: error: Tactic `rcases` failed: `x✝ : ?m.702` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-pfflzpem/.lbuild) [2.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
