## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso` states that the
induced residue-field homomorphism of a closed immersion is an isomorphism.
Its only theorem has a `sorry` proof; there are no definitions or auxiliary proofs.
The declaration docstring reproduces both steps of the node's proof, including
its stalk-surjectivity, pushforward-stalk identification, locality and quotient argument.

Hypotheses and clauses:
- Schemes Z and X: `{Z X : Scheme.{u}}`, with the universe `u` explicitly declared.
- The morphism i: Z → X: `(i : Z ⟶ X)`.
- Closed immersion: `[IsClosedImmersion i]`, the dependency's Mathlib definition.
- The point z ∈ Z: `(z : Z)`.
- The notation x = i(z): substituted directly into the canonical map's domain;
  `i.residueFieldMap z : X.residueField (i z) ⟶ Z.residueField z`.
- The induced homomorphism is an isomorphism: `IsIso (i.residueFieldMap z)`.
  This is invertibility of that specific homomorphism in CommRingCat, equivalently
  its bijectivity, not merely the existence of an unrelated field isomorphism.

Dependency declarations read and used:
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`, imported transitively.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`, from
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; a closed embedding with
  surjective stalk maps, matching the node's scheme notion.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`, from `Mathlib.AlgebraicGeometry.ResidueField`.
  The first is the residue field of the stalk, and the second is the map of
  residue fields induced by the local stalk homomorphism.
All three dependencies are Mathlib leaves and have no required Lean records.

Edge cases checked: an empty source has no z, so the pointwise assertion is
vacuous; an empty target forces an empty source. Identity morphisms give identity
residue-field maps. Nilpotent thickenings and arbitrary affine quotient closed
immersions preserve the residue field at each point. No reducedness, finiteness,
Noetherian condition, closed-point assumption or characteristic restriction is
required. The explicit arbitrary universe covers arbitrary scheme sizes in the
usual Mathlib scheme category. The node is true and needs no correction.

Searches made with `/home/ubuntu/weil-launcher/msearch.py`:
- LeanFinder: “A closed immersion of schemes induces an isomorphism on residue
  fields at each point”: eight hits, including the open-immersion instance and
  closed-immersion results about Spec of residue maps, but no exact theorem.
- Loogle: `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.Scheme.Hom.residueFieldMap`:
  zero hits.
- Mathlib grep: `residueFieldMap|residueField.*[Ii]so` in AlgebraicGeometry:
  residue-field definitions and the open-immersion instance, no closed-immersion statement.
- LeanSearch: “closed immersion scheme induced residue field map is an isomorphism”:
  unavailable (Internal Server Error); no verdict assigned to this service.
- `rg` of `residueFieldMap|residue.*[Ii]so` in WeilConjectures and lean/Sheaf:
  found `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap` in
  `WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism`. Its full signature
  assumes `[SurjectiveOnStalks p]`, not `[IsClosedImmersion p]`; it is strictly
  more general, so it does not say exactly this node's statement. Its signature
  and docstring were read. No private notion is introduced here.
- `grep -rn` of the item id in WeilConjectures: no hits.
- `rg` for the proposed name and closed-immersion/residue-field combinations in
  Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no name collision.

Source checked online because this clone has no literature/stacks-project checkout:
[Stacks Section 26.4, Tag 01HJ](https://stacks.math.columbia.edu/tag/01HJ), especially
its quotient description of stalks, and
[Stacks Lemma 29.2.1, Tag 01QO](https://stacks.math.columbia.edu/tag/01QO), the affine
quotient criterion. These support the closed-immersion input to the node's proof.
No statement dispute, missing notions or unusable dependencies were found.

## Second reading by G1

Read the sandbox node and module together with all three statement-dependency
nodes and their actual Mathlib declarations. The node's complete object,
hypothesis and conclusion list matches the Lean as follows:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Schemes Z and X | `{Z X : Scheme.{u}}` | Exact: arbitrary schemes, not affine schemes or schemes over a fixed field. |
| Morphism i from Z to X | `(i : Z ⟶ X)` | Exact: the category morphism is a morphism of locally ringed spaces. |
| i is a closed immersion | `[IsClosedImmersion i]` | Exact: closed embedding and surjective stalk maps; equivalent to the dependency node's sheaf formulation for schemes. |
| Arbitrary point z of Z | `(z : Z)` | Exact: no closed-point or rational-point assumption. |
| Put x = i(z) | `i z` in `i.residueFieldMap z` | Exact: x is an abbreviation, so no independent point or equality hypothesis is needed. |
| Residue fields of x and z | `X.residueField (i z)` and `Z.residueField z` | Exact: each is the local stalk modulo its maximal ideal. |
| Homomorphism induced by i, in direction κ(x) to κ(z) | `i.residueFieldMap z` | Exact: this is the quotient map induced by the local stalk map, with the required direction. |
| That homomorphism is an isomorphism | `IsIso (i.residueFieldMap z)` | Exact: categorical invertibility of this specific unital ring map, equivalent to its being a field isomorphism. |

The binders quantify schemes, then the morphism, its closed-immersion hypothesis,
and every source point. There are no additional implicit mathematical hypotheses.
The universe `u` is explicitly declared and arbitrary. The common universe is the
one used by Mathlib's scheme category and admits both schemes at any sufficiently
large universe; it imposes no finiteness or cardinality bound. All other names
resolve through the namespace or the explicit imports, with no free variables.

Source reading: this clone has no Stacks checkout, so I opened the actual TeX
[schemes.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/schemes.tex)
and [morphisms.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex).
In schemes.tex I read `definition-locally-ringed-space`,
`section-closed-immersion` (01HJ),
`definition-closed-immersion-locally-ringed-spaces` (01HK), and
`example-closed-subspace`: residue fields are stalk quotients, scheme morphisms
have local stalk maps, and closed-subspace stalks are quotients of ambient stalks.
In morphisms.tex I read the section introduction and `lemma-closed-immersion`
(01QO), especially conditions (2) and (4). The introduction includes local
generation of the kernel in the Stacks definition; the lemma explicitly proves
that for schemes this is equivalent to closed embedding and surjectivity alone.
Thus the Mathlib hypothesis does not drop a necessary assumption. Neither source
section assumes a base field, Noetherianity, reducedness or finite presentation.

Dependency verification: `Scheme` in Mathlib/AlgebraicGeometry/Scheme.lean is a
locally ringed space locally isomorphic to affine spectra, and `Scheme.Hom`
extends its locally-ringed-space homomorphism. These are the objects required by
def-pc-scheme. In Morphisms/ClosedImmersion.lean, `IsClosedImmersion` extends
`SurjectiveOnStalks` and adds `isClosedEmbedding`; this realizes the
def-weil-closed-immersion notion, using the equivalence just checked. In
ResidueField.lean, `residueField` is `IsLocalRing.ResidueField` of the stalk,
with its field instance, and `Hom.residueFieldMap` is
`CommRingCat.ofHom (IsLocalRing.ResidueField.map (f.stalkMap x).hom)`.
I also opened RingTheory/LocalRing/ResidueField/Defs.lean: its `ResidueField`
is literally the quotient by `maximalIdeal`. Thus def-weil-residue-field is
used as recorded, without a private substitute. Both imports are needed for
the hypothesis and canonical map. No new nodes or dependency modules are needed.

Proof docstring: step 1 retains the node's route from sheaf surjectivity to
stalk surjectivity, then the germ-defined pushforward-stalk bijection and
locality. I opened lem-weil-pbc-locally-surjective-iff-stalks and
lem-weil-pbc-closed-pushforward-stalks: their statements provide precisely the
surjectivity equivalence and clause (2) bijection used here. Step 2 retains
surjectivity of the quotient map and the inverse-image-of-maximal-ideal argument
for its zero kernel. Both steps and their node citations are present. The
module and theorem docstrings name the source and blueprint id. There is only
one declaration, its proof is `sorry`, and there are no definitions or auxiliary
proofs. The node's `lean.statement` is verbatim the theorem signature before `:=`.

Edge cases: if Z is empty the point binder makes the claim vacuous; a morphism
to empty X forces empty Z. Spec of the zero ring is included this way, without
an inappropriate field structure on a zero stalk at a nonexistent point.
For Spec(R/I) into Spec(R), including I = 0 and I = R, the same canonical
quotient-induced map has the stated behavior. Nilpotent thickenings and generic
points are included, and no nonempty or closed-point instance is assumed.
All characteristics are covered. No index set or integer n occurs, so empty
indices and n = 0 impose no additional conditions.

Independent searches, with alternative words to the worker's queries:

- LeanFinder via msearch: `quotient closed subscheme same residue field at every point`:
  eight hits concerning Spec of residue fields, canonical points and congruences;
  none with this closed-immersion hypothesis and conclusion.
- Loogle via msearch: `"residueFieldMap", "IsClosedImmersion"`: zero hits.
- LeanSearch via msearch: `closed subscheme canonical map of residue fields invertible`:
  unavailable with Internal Server Error, recorded as unavailable, without a verdict.
- Independent `rg` for residue/bijective/isomorphism combinations in Mathlib's
  AlgebraicGeometry, all WeilConjectures and repository lean/Sheaf, followed by
  focused residueFieldMap searches, found open-immersion results, algebraic
  quotient results, and the more general source lemma described below; no exact
  duplicate. Searching the proposed full-name suffix and the item id in
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found no collision.

I opened UniversalHomeomorphism.lean lines 45–63, including the section variables
and docstring of `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap`.
Its full hypothesis is `[SurjectiveOnStalks p]`, as confirmed by the class
definition in Morphisms/SurjectiveOnStalks.lean. This is strictly more general
than the node, since it has no closed-embedding hypothesis (an open restriction
is already an example outside the node's class). It is an available future
proof ingredient, but does not state exactly the node's hypothesis and therefore
does not justify replacing this delivery by an `existing: true` record under
the brief's exact-statement rule. No mathematical mismatch was found, and no
Lean or node changes were made; this second-reading section is the only repair
to the delivery. The single-file server compile completed in 1.6 seconds with
exit code 0 and no warnings.
