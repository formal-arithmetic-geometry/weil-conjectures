## Worker report

The module `Sheaf.Compactification.ProperOpenDenseIso` states
`AlgebraicGeometry.isIso_of_isProper_of_isOpenImmersion_of_schematicallyDenseOpen`.
Its proof is `sorry`; no definition or proof is supplied. The mathematical node is
unchanged, and no new nodes or dependency repairs are needed.

The previous blocked attempt mistook the NC stage-1 split for a completed stage-2
statement. The live node has `status: split` and a stage-1 review but no `lean`
record. NC's report explicitly says no compiler was run. This delivery adds that
missing stage-2 record and does not redo or change the split.

### Statement correspondence

- Schemes Z and X: `{X Z : Scheme.{u}}`, with the universe explicitly declared.
- The morphism q from Z to X: `(q : Z ⟶ X)`.
- Properness: `[IsProper q]`.
- Open immersion: `[IsOpenImmersion q]`.
- The open subscheme of X: `(U : X.Opens)`, with its canonical scheme structure
  supplied by the existing opens API.
- Scheme-theoretic density of this open: `(hU : SchematicallyDenseOpen U)`.
  The recorded definition says every restriction from an open W to W intersect U
  is injective, exactly the equivalence in Stacks 01RE. It imposes no
  quasi-compactness, reducedness, noetherianity, or nonemptiness assumption.
- Containment in the image of q: `(hUq : U ≤ q.opensRange)`.
  The order on opens is subset inclusion; `q.opensRange` is the open image of q.
- The conclusion that the particular q is an isomorphism: `IsIso q`.

Choosing an arbitrary witness U with the two displayed properties is the usual
binder form of the node's existence hypothesis: any such witness yields `IsIso q`.
No condition on the witness is added. All variables and universes are bound with
`autoImplicit` and `relaxedAutoImplicit` disabled.

### Dependency declarations read and used

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`; read their full
  definitions and docstrings, including the locally ringed space structure.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`; read the class extending separatedness, universal
  closedness and locally finite type. Universal closedness implies quasi-compactness,
  as the existing dependency record explains.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; read the abbreviation in terms of open
  immersions of locally ringed spaces.
- `def-trf-schematically-dense-open`:
  `Sheaf.TraceFormula.SchematicallyDenseOpen`,
  `AlgebraicGeometry.SchematicallyDenseOpen`; read its entire definition/docstring.
  It is used directly, with no duplicate definition.
- Proof dependency `lem-weil-pbc-proper-closed-image`:
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed`,
  `AlgebraicGeometry.Scheme.Hom.isClosedMap`. The Proper import already imports this
  module; its result is described in the theorem's proof docstring. The other
  proof dependencies are the definition modules publicly imported for the statement.

The theorem docstring follows all three reviewed proof steps: the image is open
and closed; restriction injectivity on the open complement forces zero stalks,
contradicting nontrivial local rings; the image is therefore the full target and
an open immersion onto it is an isomorphism.

### Edge cases

Checked the empty target and source: an open immersion into the empty scheme is
an isomorphism; an empty schematically dense U forces the target empty. A proper
clopen component inclusion with nonempty complement fails hU, so cannot give a
false positive. Nilpotents cause no problem because density is injectivity on
sections, not just topological density. The open D(t) in Spec k[t] is dense but
not proper, showing the properness hypothesis has content. The identity satisfies
properness and open immersion, and the conclusion applies to every permitted U.
No quasi-compactness is imposed on U, including when the target is not
quasi-compact.

### Searches made

Read the current main-20261015 blueprint statement and proof and Stacks
`morphisms.tex`, definitions/lemmas for Tags 01RB and 01RE. The blueprint statement
and the DAG statement agree verbatim.

Actual msearch.py calls are retained in `searches.jsonl`:

- LeanFinder: "A proper open immersion whose image contains a schematically dense
  open subscheme is an isomorphism": eight results, including
  `isIso_of_isOpenImmersion_of_opensRange_eq_top` and
  `isIso_iff_isOpenImmersion_and_surjective`; none supplies this item's hypotheses.
- Loogle: `AlgebraicGeometry.IsOpenImmersion, AlgebraicGeometry.IsProper`:
  zero hits.
- Mathlib grep: `isIso.*[Dd]ense|[Dd]ense.*isIso|IsProper.*IsOpenImmersion`,
  subdirectory `AlgebraicGeometry`: zero hits.
- LeanSearch: "A proper open immersion with dense image is an isomorphism":
  eight results, giving only the final open-immersion identification or
  isomorphisms onto the open image, not the entire statement.

Direct rg searches of Mathlib/AlgebraicGeometry, WeilConjectures and Sheaf used
`proper.*dense|dense.*proper|isIso.*[Dd]ense|[Dd]ense.*isIso|SchematicallyDense`,
and the exact blueprint id. The upstream module
`WeilConjectures.Compactification.IsomorphismNearClosure` contains
`AlgebraicGeometry.isIso_of_isProper_of_isOpenImmersion` (lines 753 onward).
I read its full signature, docstring and proof: it requires
`[QuasiCompact D.ι] [IsSchemeTheoreticallyDominant D.ι]`. This is the restricted
quasi-compact version, so recording it as an exact existing declaration would
silently add an assumption. This delivery uses the unrestricted recorded density
notion and a distinct name. Searches of Sheaf found the existing density
definition and consumers, but no full theorem. The new fully qualified name is
absent from both project trees, and its compilation succeeds.

### Validation

Compiled this module with the prescribed scompile.py against the live published
server build. Both the sandbox and library-name compilations succeeded, with no
errors or unexpected warnings. No global build or direct repository mutation was
run. No statement dispute, statement correction, or missing dependency remains.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
