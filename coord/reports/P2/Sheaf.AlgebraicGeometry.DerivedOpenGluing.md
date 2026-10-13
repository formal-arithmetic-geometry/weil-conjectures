## What changed

Reduced `AlgebraicGeometry.derived_open_gluing` without changing its signature or any
existing public import, definition, or target. The main module now uses object gluing,
checks compatibility of the composites by a proved private categorical helper, and applies
a proved scheme-level Hom lifting theorem. It has no `sorry`.

Added three modules, one public theorem per module:

- `Sheaf.AlgebraicGeometry.DerivedOpenGluingObjects`: the object and transition portion
  of the original cone/split-restriction argument, with no morphism-lifting clause.
- `Sheaf.AlgebraicGeometry.SchemeDerivedHomRestrictionTransport`: the comparison between
  localized-site Hom restriction and the scheme restriction used in the original signature,
  for a single nested pair of opens and arbitrary local morphism. It has no cover or gluing claim.
- `Sheaf.AlgebraicGeometry.SchemeDerivedHomGluing`: a complete proof lifting compatible
  local maps between two already-global objects, from the restriction comparison and the
  existing `derived_hom_mayer_vietoris`. It constructs the localized derived categories
  directly by transporting the given localization along the equivalence on complexes.
  It chooses no object from an unproved existence theorem. Exactness produces the lift;
  naturality and full-faithful cancellation prove its two scheme restriction equations.

Updated the parent node's proof, proof dependencies and proof origin; added nodes for all
three public theorems. This preserves the original cone and Mayer–Vietoris route. The unit
`sk-thm-picard-duality` has no realized nodes that this reduction bypasses.

The source files under literature are absent on this machine; read the actual source at
[Stacks 08DG](https://stacks.math.columbia.edu/tag/08DG) and
[Stacks 08BW](https://stacks.math.columbia.edu/tag/08BW). The object proof is the first
assertion of 08DG; Hom lifting uses exactness at the local pair in 08BW.

Validation: all four sandbox modules compile in import order using the required local
compiler. No existing signature changed. The final required deliver3 dry run is the gate
for the delivery.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.derived_open_gluing`
(`lem-sc-derived-open-gluing`) by a complete Lean proof from strictly smaller intermediate
statements. Added exactly two holes:

- `AlgebraicGeometry.derived_open_gluing_objects`
  (`lem-sc-derived-open-gluing-objects`), in DerivedOpenGluingObjects.
- `AlgebraicGeometry.scheme_derived_hom_restriction_transport`
  (`lem-sc-scheme-derived-hom-restriction-transport`), in SchemeDerivedHomRestrictionTransport.

Both are public named theorems with `:= by sorry`, source, complete proof in words,
matching DAG node, and a separate module. No other delivered declaration has `sorry`.
In particular `AlgebraicGeometry.scheme_derived_hom_gluing` is proved from the existing
Mayer–Vietoris theorem and the smaller transport identity. The private helpers
`compatible_composites`, `lifted_morphism_eq`, and the explicit localization transport
construction are proved without holes.

This is a decomposition, not an unconditional proof of 08DG. Original holes closed: 1;
new holes added: 2; raw net: -1. The ledger must compute the actual pinned-closure net.
The new transport hole is a coherence identity for one inclusion, not a renamed Hom lift;
the object hole has neither a target E nor a lifting assertion.

Edge cases checked mathematically: an empty open, empty overlap, U=V=top, W=U, and zero
local maps. No nonemptiness, separation, boundedness or quasi-coherence assumption was
added. No uniqueness of the global lift is asserted. For disjoint opens the overlap
condition lies in the zero derived category; for W=U the transport assertion is unit
naturality. These cases are consistent with the stated source arguments.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
and `Sheaf.Paper.DerivedHomMayerVietoris` from the main module. The first is retained in
the object-gluing module for its original cone restriction argument; the second remains
available through the existing public import in DerivedCategory and is used by the proved
Hom lifting theorem. Redundant direct Paper.DerivedHomMayerVietoris imports in the new
modules were removed too.

No existing DAG node or library module becomes unnecessary to the overall argument:
`def-weil-abstract-derived-category` and `lem-pc-restrict-derived-direct-image-open` are
needed by object gluing, and `lem-sc-derived-hom-mayer-vietoris` is used by Hom lifting.
Their direct edges in the parent have moved to the appropriate smaller nodes. Thus no
whole-library module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original Hom input is stated on localized sites, whereas the original gluing signature
uses open-subscheme module categories and explicit canonical comparisons. Applying that
input directly omits a nontrivial transport/coherence step. The new single-inclusion
transport theorem isolates that step rather than silently assuming the two formulas agree.
The proof constructs the additional localized-site derived-category instances in the given
morphism universe; the original assumptions only supply the open-scheme instances.

The legacy node's source.document still names perfect.tex even though its tag and proof
origin name cohomology.tex. No change to that non-worker-owned field is delivered; all new
nodes use cohomology.tex. No mathematical statement is disputed or changed.

An initial application and destructuring in one obtain command exhausted elaboration
heartbeats. Binding the application first and then destructuring it compiled, without an
increased budget or a definition change.

## New nodes

`lem-sc-derived-open-gluing-objects`: source 08DG first assertion and original proof steps
1–2, inheriting the original triangulated cone and open direct-image restriction inputs.
Strictly smaller than the original theorem because it has no morphism-lifting assertion.

`lem-sc-scheme-derived-hom-restriction-transport`: source 08BW canonical restriction maps,
with the comparison expressed using the existing Mathlib derived composition and natural
isomorphisms. It asserts one transport identity for W contained in U; it constructs neither
a glued object nor a global morphism. Its proof includes the localization comparison
check and the naturality calculation needed to finish it.

`lem-sc-scheme-derived-hom-gluing`: source 08BW exactness at the local Hom pair. Already
proved in the delivery, conditional on the preceding transport identity and the existing
Mayer–Vietoris input. It applies to two global objects and has no object descent data.

Searches were actually run and are recorded in searches.jsonl: LeanSearch was unavailable;
LeanFinder returned underived gluing/restriction results; Loogle found overFunctorMap;
Mathlib grep found no matching derived assertion. The DAG and whole blueprint were also
searched for existing object-gluing and transport nodes. No duplicate was found.
No statement or definition change record and no forced adaptation is needed.

## Second reading by P2

1. **Existing interface — pass.** Read the repository and sandbox versions of
   DerivedOpenGluing in full and compared their diff. The entire signature of
   `AlgebraicGeometry.derived_open_gluing`, from `theorem` to `:= by`, is byte for
   byte identical. Its public DerivedCategory import, universes, instances and
   docstring are unchanged. The only existing-node fields changed are `proof`,
   `proof_deps` and `proof_origin`. There are no adapted existing modules,
   changed definitions, changed target statements or change records.
2. **Proof and trust — pass, conditional decomposition.** Independently compiled
   all four modules in import order with lcompile.py: 32.8, 18.5, 35.3 and 40.0
   seconds, respectively, without errors or warnings. Scanned every delivered
   Lean file: exactly the two reported named theorem holes remain, and no
   forbidden declaration or hollow definition occurs. A scratch import file
   printed the axioms of all four public theorems: precisely `propext`,
   `Classical.choice`, `Quot.sound` and `sorryAx`. Thus the upper theorem and
   Hom lifting theorem are proved conditional on open inputs, not axiom-free
   completed results. Read `compatible_composites` and `lifted_morphism_eq`:
   the former substitutes the local compatibility equation and composes the
   transition equation; the latter uses naturality and faithful preimage
   cancellation. `derivedCategoryTransport` constructs its category and
   localization functor explicitly from the supplied category and cochain
   equivalence, with the localization property proved by
   `Functor.IsLocalization.of_equivalence_source`. It takes no arbitrary data
   from an unproved existence theorem. Destructuring object gluing occurs only
   in the proof of an existential proposition.
3. **New statements — pass after one proof-plan correction.** Read
   [Stacks 08DG](https://stacks.math.columbia.edu/tag/08DG),
   [08BW](https://stacks.math.columbia.edu/tag/08BW), and
   [08FE](https://stacks.math.columbia.edu/tag/08FE), and the definitions and
   comparisons in DerivedHomMayerVietoris and ExactFunctor. Object gluing has
   exactly the cover, two objects and transition data of the first assertion
   of 08DG; it omits the morphism clause and is strictly part of the argument.
   The transport statement has one inclusion and one local map, and equates
   two canonical restrictions by conjugation. Its qU inverse/hom and qW
   hom/inverse orientations match their source and target objects; it asserts
   neither object gluing nor a global lift. Hom gluing applies exactness at
   the local pair in 08BW, with no uniqueness claim. Checked empty opens,
   empty overlap, U=V=top, W=U, and zero maps: unit cancellation handles W=U;
   empty overlap imposes no extra condition; zero maps are preserved by all
   restrictions and conjugations. No boundedness or quasi-coherence premise
   is needed. Both remaining holes have source and full proof docstrings and
   matching nodes. Repeated searches with different terms: LeanFinder on
   derived composition coherence returned ordinary derived-functor comparison
   lemmas; Loogle did not know the upstream mapDerivedCategoryNatIso name;
   Mathlib grep on descent/glue/gluing returned underived and unrelated
   descent. Searched repository Sheaf and WeilConjectures for complex gluing,
   descent and the exact derived comparison names, and read the existing
   OpenDerivedMatePresentation comparison proof. No existing result states
   either hole. Closing the transport hole requires a new localization
   coherence calculation, rather than an immediate application of those
   comparison-factorization lemmas; neither hole has a few-minute proof found.
4. **Route and pruning — pass.** The main proof first obtains F, iU, iV and
   their transition, proves compatibility of the composed local maps, then
   applies Hom lifting. Hom lifting transports the maps, cancels the overlap
   equivalence, and uses the existing derived_hom_mayer_vietoris exactness.
   The unit sk-thm-picard-duality has empty realized statement and step lists;
   no realized node is bypassed. Every old direct proof dependency is
   accounted for in No longer needed: the cone and direct-image inputs move
   to the object node, and Mayer–Vietoris moves to Hom lifting. The original
   public import remains needed for the signature. All added imports are
   private when used only by proofs; the object module retains its planned
   direct-image input. No whole-library module pruning is claimed.
5. **DAG agreement — pass after repair.** Checked all four proof-step `uses`
   unions against `proof_deps`, and checked each new node's recorded Lean
   signature byte for byte against its module. The parent records precisely
   object gluing, elementary composition compatibility, and Hom lifting.
   The Hom node records explicit localization transport, the transport
   identity, exactness, and cancellation, as the code does. The transport
   node records the single-inclusion comparison calculation still to prove.
   Found one inherited sign inconsistency in the object node: step 1 named
   the positive V restriction while step 2 and the Lean docstring used the
   difference map. Changed step 1 to **minus** the V restriction, so the
   kernel equation gives the prescribed transition c. This changes the
   natural-language proof plan only, not any mathematical statement or Lean
   code. The legacy source-document mismatch noted above remains reported.

Second reading changed the object node's cone-map sign and appended this review.
No Lean repair was necessary. Holes closed remain 1, holes added remain 2;
this delivery is a decomposition with raw net -1, not a claimed net proof gain.
