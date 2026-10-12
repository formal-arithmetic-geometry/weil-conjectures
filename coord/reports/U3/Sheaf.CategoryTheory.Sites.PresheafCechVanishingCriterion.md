## What changed

Replaced the single sorry in `Sheaf.CategoryTheory.Sites.PresheafCechVanishingCriterion`
by a complete Lean strong induction on degree, simultaneously over every small-valued
presheaf, followed by specialization to the representable presheaf. The existing theorem
signature and docstring are unchanged. Two proof-only imports expose the local-killing
and edge-injectivity steps of the original plan as separate items.

Added `Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling` and
`Sheaf.CategoryTheory.Sites.PresheafCechExtEdgeInjective`, one public theorem each.
Updated the parent node's proof, proof_deps and proof_origin to match the Lean reduction.
No existing definition, statement or public import changed. The unit sk-prop-cd has no
realized statement or step nodes, and its route is unchanged.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.Sheaf.isZero_H'_of_presheafCech_vanishing`
(node `lem-sc-presheaf-cech-vanishing-criterion`). Its proof combines the two new lemmas,
the induction hypotheses, Ext.comp_zero, and AddCommGrpCat.isZero_of_subsingleton.
No sorry remains in the assigned module.

Added two holes:

- `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing`
  (`lem-sc-presheaf-free-ext-local-killing`): local effacement of one positive Ext class;
  it has no Cech-vanishing assumption.
- `CategoryTheory.Sheaf.presheafCech_ext_edge_injective`
  (`lem-sc-presheaf-cech-ext-edge-injective`): injectivity for one locally surjective map
  in one degree, assuming lower positive Ext rows vanish and Cech cohomology in that
  degree vanishes. It does not assert global vanishing or perform the induction.

This is a decomposition: one original hole closed, two strictly partial holes added;
net holes closed minus added is -1. The target still depends on sorry through these lemmas.
Each new hole has its source and full proof in words in its docstring and its own DAG node.
The existing set nerve resolution remains a dependency, with its original hole unchanged.

Local compilation of all three modules passed. The main theorem also compiled separately
against the sandbox's compiled intermediate modules. The required delivery dry run is the
final gate.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicTopology.SetCechNerveFreeResolution`
from the assigned module. Its node `lem-weil-pbc-set-cech-nerve-free-resolution` is now
used by the edge-injectivity intermediate and remains imported there: it is not pruned
from the target closure. No node or module of the original mathematical route is obsolete;
pruned modules: none. Both original public imports are retained because the signature
uses presheafCechComplex and H'.

## Where the brief, the DAG or earlier work was wrong

The original node marks its local-killing step elementary, but finite Yoneda representation,
local lifting, and the free/sheafification adjunction argument are substantial and have no
matching usable theorem in the pinned Mathlib. The spectral-sequence step likewise is not
supplied by the set-level free nerve resolution alone. The two new items expose these gaps;
the original plan's actual strong induction is now implemented in the parent module.

Searches: LeanFinder returned cohomologyPresheaf, H, Mayer-Vietoris and K-injectivity results;
Loogle supplies Ext composition and zero lemmas; grep found no local-killing or presheaf
Cech edge theorem. LeanSearch returned Internal Server Error and is recorded as unavailable.
The existing WeilConjectures CechCriterion needs extra EnoughInjectives, coefficient universe
and slice-product assumptions, so it cannot prove this signature unchanged.

The cited local Stacks TeX files are absent in this clone. Read the primary sources online:
[03F9](https://stacks.math.columbia.edu/tag/03F9),
[079Z](https://stacks.math.columbia.edu/tag/079Z),
[01GC](https://stacks.math.columbia.edu/tag/01GC), and
[06XU](https://stacks.math.columbia.edu/tag/06XU).
The latter supplies finite Yoneda representatives without enough injectives. The original
plan's Yoneda variant of the descent filtration remains the content of the new edge item.

Edge cases checked for the new statements: q=1 has no intermediate rows; the identity
presheaf map gives an identity edge map; F=0 gives zero groups; an empty target presheaf
has zero free abelian sheaf. An empty source locally covering P makes the sheafified free
augmentation zero, consistent with an injective map from the zero Ext group. The induction
never invokes its degree-zero case, and values and fibre products stay in Type v.

## New nodes

`lem-sc-presheaf-free-ext-local-killing`: the original first step, for one Ext class, sourced
from Tag 06XU and the local-lifting argument in Tag 03F9. Its module is
`Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling`.

`lem-sc-presheaf-cech-ext-edge-injective`: the original exact-nerve/descent step and its
finite-filtration consequence, sourced from Tags 079Z and 01GC. Its module is
`Sheaf.CategoryTheory.Sites.PresheafCechExtEdgeInjective`; it retains the original set
nerve resolution as a proof dependency. Neither new node depends on the assigned module.
No change records or forced adaptations are needed.

## Second reading by U3

1. Compared every delivered module with the repository. The only existing module is
   PresheafCechVanishingCriterion: its declaration signature is byte-identical, its
   original docstring is unchanged, and its public imports are unchanged. Its changes
   are the proof and two private proof imports replacing the old private import.
   The other two modules are new. No definition or existing statement changed, no
   forced adaptation or change record is needed. Verdict: pass.
2. Compiled all three files with lcompile.py in import order. Inspected all delivered
   Lean text: the only sorries are the two named intermediate theorems listed above;
   there are no definitions, forbidden declarations or data chosen from an unproved
   existence theorem. Scratch copies with #print axioms for each of the three
   declarations show exactly propext, Classical.choice, Quot.sound and sorryAx.
   The main induction really combines local killing with edge injectivity and then
   specializes to yoneda.obj U. Verdict: pass as a decomposition, not a closed proof.
3. Read both intermediate statements and their docstring proofs against the primary
   Stacks pages 06XU, 079Z, 01GC and 03F9. Local killing constructs the presheaf of
   generator lifts and uses a split pullback; it has no Cech-vanishing hypothesis.
   Edge injectivity assumes vanishing only in lower positive Ext degrees and one
   Cech degree for one locally surjective map. Neither implies the target on its own
   or repeats its hypotheses and conclusion. Checked q=1 (no lower rows), identity
   maps, zero coefficients, and empty presheaves; local covers need not be pointwise
   surjective, which is why the objectwise-image step precedes sheafification.
   The small-value universes are preserved by the subtype and finite fibre products.
   Independent LeanFinder queries on effacement by epimorphisms and on injectivity
   from exact augmented resolutions found Ext exact-sequence and resolution APIs,
   not either intermediate. Loogle on Ext/epi found only general API; rg in the
   library and Mathlib's Ext files found no matching theorem. Read the existing
   CechCriterion: its slice-product, universe and injective hypotheses prevent direct
   use here. The two substantial holes cannot be closed by those APIs in a few
   minutes. Verdict: true, needed, strictly partial statements; no duplicate found.
4. Read the original plan and dag/units/sk-prop-cd.json. The local-killing,
   augmented-nerve, lower-row induction and representable-specialization route stays.
   The unit's realized statement and six step lists are empty and unchanged. Both
   new imports in the parent are proof-only; public imports of new modules supply
   names in their signatures. The free-nerve resolution remains a proof dependency
   of the edge lemma, so its import is retained there. The No longer needed section
   accounts for every old proof dependency absent from the new direct dependency
   list. No target-closure module is claimed pruned. Verdict: pass.
5. Checked the parent node's changed fields: only proof, proof_deps and proof_origin
   differ. In all three nodes proof_deps is exactly the union of the proof steps'
   uses. New nodes contain source, natural-language argument, search records,
   creation/blueprint/unit/chapter metadata and Lean records. Checked the two new
   recorded Lean signatures against their source verbatim. Verdict: pass.

Second-reading changes: expanded the new edge lemma's docstring and node proof with
an explicit finite dimension-shifting argument, using kernels of its exact augmented
nerve and the Yoneda Ext long exact sequences. This supplies the previously abbreviated
justification that no enough-injectives hypothesis is needed: a kernel class lifts to
a map on the (q-1)st kernel; degree-q Cech vanishing extends that map to the previous
nerve term, so its connecting class is zero. No Lean statement or proof
term changed; no further hole closed or added. One original hole is closed and two
holes are added (net -1), as reported above.
