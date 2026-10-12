## What changed
`Sheaf.AlgebraicGeometry.ArtinSchreierData`: replace the original sorry by a reduction
combining natural section identifications with existence of the two maps for those
same identifications. The existing signature and docstring are byte for byte unchanged.
The helpers are proof-only imports. Remove unused imports; the redundant public
ShortExact import remains publicly exported through Kummer. Locally suppress the
unused-variable linter for the unchanged existential binder `hzero`.

`Sheaf.AlgebraicGeometry.ArtinSchreierDataConstruction`: new, still-open theorem
`AlgebraicGeometry.artinSchreier_construction` supplies a sheaf, its isomorphism to the
recorded lifted structure-module sheaf, and natural additive section equivalences.
It works for every scheme; it does not mention the Artin--Schreier maps or characteristic.

`Sheaf.AlgebraicGeometry.ArtinSchreierDataFormulas`: new, still-open theorem
`AlgebraicGeometry.artinSchreier_formulas` constructs wp and iota for a sheaf equipped
with natural section equivalences, and proves their formulas and zero composite.
Its new docstring specifies the actual construction and the sheafification argument.

The import and linter change is recorded in
`coord/changes/ArtinSchreierData-imports.md`. No existing definition changes.

## Proved and sorry left
`AlgebraicGeometry.artinSchreier_data`: the original named sorry is replaced by a
compiled proof from the two strict intermediate statements. This is a reduction,
not an axiom-free completion of the construction.

Sorries remain only as the entire proofs of:
- `AlgebraicGeometry.artinSchreier_construction`, node
  `lem-sc-as-sequence-construction-helper`, module ArtinSchreierDataConstruction.
- `AlgebraicGeometry.artinSchreier_formulas`, node
  `lem-sc-as-sequence-formulas-helper`, module ArtinSchreierDataFormulas.

Local compilation of all three modules passes without errors or warnings.
A scratch copy with #print axioms for all three declarations reports only propext,
Classical.choice, Quot.sound, and sorryAx. The scratch copy was removed.
No axiom, unsafe, opaque, extern, implemented_by, or sorry in a definition occurs.

## No longer needed
The original direct proof dependency `lem-sc-as-sequence` is no longer used by this
node. Its module `Sheaf.AlgebraicGeometry.ArtinSchreierSequence` remains a consumer
of this datum and is not globally pruned. The old dependency pointed back to that
consumer; the new proof dependencies are the two helper nodes, with no such cycle.

Removed imports from ArtinSchreierData:
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact` (redundant public import;
  still exported by Kummer).
- `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk` (kernel/exactness, not data).
- `Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent` (redundant; publicly reached by
  EtaleTensorSectionsSheaf and still needed there).
- `Sheaf.RingTheory.LocalRing.ArtinSchreierKernel` (kernel/exactness, not data).
- `WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier` (unused in this reduction).
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint` (stalk/exactness, not data).

The original node had no other proof_deps to remove. No unit-level node is bypassed:
`dag/units/sk-prop-h2.json` has empty realized.statement and realized.steps entries;
this construction implements the maps paragraph below the unit level.

## Where the brief, the DAG or earlier work was wrong
The first worker's formulas helper quantified over arbitrary wp, iota, and arbitrary
additive section identifications without naturality. It was false. For example, in
characteristic 2 take a curve over an algebraic closure of F_2, its usual function
sheaf and identifications, and wp = 0. A constant alpha with alpha^2 + alpha + 1 = 0
satisfies alpha^2 - alpha = 1, contradicting the claimed formula for wp. Likewise,
iota = 0 cannot satisfy the required formula for c = 1 on a nonempty object.
The revised helper requires naturality and existentially constructs the maps.

The first worker's node lean.module values omitted their final letters, lean.statement
contained prose rather than the signature, and each helper proof_deps cited the whole
item, producing a circular plan. These records are repaired. The original docstrings
were proof sketches without the needed compatibility; the new helper docstrings give
complete natural-language constructions. The item node now records the actual Lean
reduction, not the original bundled consumer as its proof dependency.

## New nodes
`lem-sc-as-sequence-construction-helper`: identifies the recorded tensor-sections
sheaf naturally with regular functions. Its proof plan explicitly uses the existing
structure-module pullback isomorphism and normalized restriction definitions, not
the entire Artin--Schreier result. Matching Lean module ArtinSchreierDataConstruction.

`lem-sc-as-sequence-formulas-helper`: constructs the Frobenius-minus-identity and
constant-sheaf maps for an arbitrary naturally identified function sheaf. Its plan
uses positive field characteristic, the characteristic-p binomial formula, canonical
ZMod casts, Fermat, and the sheafification universal property. Matching Lean module
ArtinSchreierDataFormulas. Neither lemma restates the entire item.

Real independent searches recorded by msearch: LeanFinder for natural structure-sheaf
section identifications, Loogle for Frobenius ring homomorphisms, and grep for Frobenius
and sheafification lift APIs. LeanSearch was unavailable (Internal Server Error),
recorded honestly. The results include Mathlib's frobenius/map_frobenius,
sheafifyLift/toSheafify_sheafifyLift/sheafify_hom_ext, and structure-sheaf pullback
APIs; none states either complete helper with the recorded tensor-pullback restrictions.
Also searched lean/Sheaf and the upstream etaleStructurePresheaf and module files.
The upstream sheaf proof uses a Hom-valued module pseudofunctor rather than the tensor
section presheaf, so it is not the required natural identification without comparison.

Change record: `coord/changes/ArtinSchreierData-imports.md`.

## Second reading by K1
1. Compared the delivered item with its repository version using diff, and checked
   the declaration substring from `theorem artinSchreier_data` to `:=` for exact byte
   equality. Pass: existing signature, hypotheses, conclusion, and definitions are
   unchanged. Helper statements are new, unpublished statements repaired before
   delivery; no existing target is changed. Public-import removal and the local lint
   option are declared in the import change record, with all transitive importers.
2. Compiled all three files in import order through lcompile.py. Pass without warnings.
   Inspected every proof and searched forbidden constructs. Exactly the two listed
   public named helper theorems remain sorry-backed; no definition contains sorry.
   #print axioms in a removed scratch copy showed only the three permitted axioms
   plus sorryAx attributable to the still-open helpers. The reduction itself uses
   their exact witnesses and no axiom escape.
3. Rejected the false arbitrary-maps helper, with the characteristic-2 counterexample
   above. Repaired it to require naturality and construct the maps existentially.
   Checked p = 0 is excluded, p = 1 cannot be the characteristic of a field, and p = 2
   and the empty étale object cause no problem: empty-object section rings are zero
   and all formulas still hold. No nontriviality of those section rings is assumed.
   The construction lemma is independent of characteristic; each helper is strictly
   part of the argument. Each has a full source-based docstring proof, self-contained
   node, verbatim Lean signature, and genuine independent searches. Neither is an
   existing complete result nor a renaming of the item. Closing either completely
   requires the natural tensor-pullback comparison or the sheafification construction;
   neither is a few-minute direct application of a found lemma.
4. Reviewed from the item downward. The proof is the elementary combination of the
   natural section identification and map construction, exactly the maps paragraph
   of the source. Retained the existing tensor-sheaf definitions; no hollow replacement.
   Pruned all unused original proof imports and the redundant ShortExact public import,
   recording every old proof_deps entry no longer used. The unit route remains intact;
   no realized unit node is dropped. Remaining public imports supply signature names;
   the construction helper's additional tensor-pullback import is proof-only.
5. Repaired lean.module spelling, verbatim lean.statement, self-contained statement,
   stmt_deps, proof steps, proof_deps union, sources, searches, and proof_origin of the
   new nodes. Updated the item's proof/proof_deps/proof_origin to the compiled
   two-step reduction. The helper plans no longer depend on the item. Pass.

Second reading changed: replaced the false split by a natural-identification/maps
reduction, completed both proof docstrings, repaired all node metadata and circular
plans, pruned unused imports, and documented the redundant-public-import/linter change.
