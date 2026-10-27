## Worker report

The module `Sheaf.TraceFormula.SplitNodeAlgebraizationFiniteType` states
`AlgebraicGeometry.split_node_algebraization_finite_type`, with its sole proof `by sorry`.
It introduces no definitions. The node statement is unchanged.

Hypothesis and conclusion correspondence, with the node and source open:

- Schemes Z and B: `{Z B : Scheme.{u}}`; the map is `g : Z ⟶ B`.
- Flat and locally finitely presented: `[Flat g] [LocallyOfFinitePresentation g]`.
- Affine base: `[IsAffine B]`. Finite type over Spec Z is the structure map
  `bZ : B ⟶ Spec (.of (ULift.{u} ℤ))` with `[LocallyOfFiniteType bZ] [QuasiCompact bZ]`.
  The universe lift is an isomorphic copy of the integers, not a restriction on B.
- Point z and its image b: `(z : Z)` and the term `g z`, respectively.
- The induced κ(b) → κ(z) is an isomorphism: `Function.Bijective (g.residueFieldMap z).hom`.
- The scheme-theoretic fibre is `g.fiber (g z)` and its marked point is `g.asFiber z`.
  `formalNodalCompletedStalk` is exactly maximal-ideal-adic completion, and
  `formalNodalPowerSeriesQuotient (B.residueField (g z)) 0` is κ(b)[[u,v]]/(uv-0).
  `hsplit` is `Nonempty (@AlgEquiv ... (formalNodalFiberCompletionAlgebra g z) inferInstance)`.
  The specified algebra structure is the canonical κ(b) action through the fibre projection,
  its stalk map, and completion; it is not an arbitrary coefficient structure.
- T, Y, and Y → T: `nodalBase`, `nodalModel`, `nodalModelBaseMap` from the existing
  `def-trf-universal-nodal-model` record. Its rings are Z[a] and Z[a][u,v]/(uv-a).
- Schemes V,U and points v,q: the first four existential binders in the conclusion.
- The morphism τ is parametrized by its section h: `(h : Γ(V, ⊤))`, with τ the explicit
  `nodalBaseMap h`. This is equivalent to quantifying τ: polynomial evaluation and the
  Γ–Spec adjunction give a bijection between maps V → Spec Z[a] and global sections h.
  Its inverse is pullback of a. Thus no extra condition on τ or h is imposed.
- Pointed e:(V,v) → (B,b), p:(U,q) → (Z,z): `e`, `p`, `e v = g z`, `p q = z`.
  Their étaleness is `Etale e ∧ Etale p`.
- The structure map is `w : U ⟶ V`, with `w q = v` and `w ≫ e = p ≫ g`.
- The étale V-morphism m has the exact type
  `U ⟶ pullback nodalModelBaseMap (nodalBaseMap h)`, with `Etale m` and
  `m ≫ pullback.snd nodalModelBaseMap (nodalBaseMap h) = w`.
- Both induced residue maps, rather than abstract field equivalences, are isomorphisms:
  `IsIso (e.residueFieldMap v) ∧ IsIso (p.residueFieldMap q)`.
- The final canonical relative-Spec identification is explicit in the last conjunct.
  For every affine open A of V its inverse image under the target projection is affine,
  and its section ring is isomorphic to `formalNodalModelRing Γ(V,A) (h|A)`.
  The equivalence φ sends the pulled-back coefficient c to `algebraMap ... c` and each
  universal coordinate k:Fin 2 to the quotient class of `MvPolynomial.X k`.
  Here h|A is exactly `V.presheaf.map (homOfLE le_top).op h`. The coordinate on the
  target is obtained from `Scheme.ΓSpecIso`, `pullback.fst.appLE`, and the universal
  quotient class, not an arbitrary section. Since coefficients and these two generators
  generate each polynomial quotient, these equivalences are unique and automatically
  agree under restrictions. This is precisely the canonical identification with
  Spec_V(𝒪_V[u,v]/(uv-h)), stated through its affine charts; there is no chosen unrelated
  isomorphism or missing gluing compatibility.

Dependencies used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map`; `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `asFiber`,
  `fiberToSpecResidueField` (the latter through the canonical completion algebra).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`;
  `...Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`;
  `...Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `...Morphisms.QuasiCompact`: `QuasiCompact`; `...Morphisms.Etale`: `Etale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.snd`,
  `pullback.fst`; `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`;
  `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`;
  `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`.
- `Sheaf.TraceFormula.FormalLocalStructureNodalFamily`: `formalNodalCompletedStalk`,
  `formalNodalPowerSeriesQuotient`, `formalNodalFiberCompletionAlgebra`,
  `formalNodalModelRing`. Their new definition owner
  `def-trf-formal-nodal-model-constructions` is cited in stmt_deps;
  `lem-trf-formal-local-structure-nodal-family` remains only a proof dependency.
- `Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel`: `nodalModelBaseMap`,
  `nodalBaseMap`, `nodalModelRing`, with their defining rings and maps. These plain
  definitions have their own landed owner `def-trf-universal-nodal-model`, which is added
  to stmt_deps. Its theorem is not used in the proof. The formal-model definitions have
  their own new owner described under New nodes; no dependency module is rewritten.

All recorded statement dependencies were read, including their full signatures and
construction docstrings in the local Lean sources. The stated proof dependencies are
imported, either publicly when their constructions occur in the signature, or as plain
proof imports. The five-step docstring follows the node's proof, including localization
of the parameter map and the coefficient-preserving relative-Spec gluing.

Import-cycle notice for the maintainer: the definitions owned by
`def-trf-universal-nodal-model` physically remain in the parent theorem module
`Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel`. Consequently that parent
module must omit the future proof import of this new module, as allowed by stage 2 §3(7).
There is no DAG dependency cycle: the universal-model definition node depends only on
polynomial/scheme definitions, not on its containing module's theorem. No live file was
edited or moved.

Edge cases checked before and after writing: h=0 and nilpotent h are included; no
invertibility or reducedness is assumed. Characteristic 2 is included (no division by 2).
The point b need not be closed in B. The affine base may be nonreduced. An empty Z or B
has no z and so creates no false existence assertion. The affine-open clause includes
the empty open (zero section ring and its zero-ring polynomial quotient). No algebraic
closure, relative-dimension, global Noetherianity of Z, separatedness, or extra equality
of universes is assumed. The universal chart is lifted to the same scheme universe u.

Searches (all performed using the prescribed wrapper or direct read-only rg):

- msearch leanfinder: “A split nodal point in a flat locally finitely presented scheme
  over an affine finite type integer base has a common etale chart uv equals h”. Eight
  hits, including StandardEtalePresentation and standard-smooth presentations; no exact
  rational split-node algebraization statement.
- msearch loogle: `AlgebraicGeometry.Etale, AdicCompletion`: zero hits.
- msearch grep in AlgebraicGeometry: `nodal|Artin.*approximation|relative.*completion.*etale`:
  zero hits.
- msearch leansearch: “universal nodal family Spec Z u v a quotient uv minus a and its
  base change”: eight general Spec Z/affine-space results; no exact nodal family.
- msearch leanfinder: “universal nodal family xy equals parameter over Spec integers
  polynomial”: eight elliptic-coordinate results; no exact universal nodal family.
- msearch grep `nodal|uv.*a` in AlgebraicGeometry: unrelated hUV variable matches.
- Direct rg of `lean/WeilConjectures` for nodalBase/nodalModel and the item id: no
  implementation of this statement. Direct rg of `lean/Sheaf` found the universal
  family and formal-completion helpers cited above, and the more general parent theorem;
  the latter has different hypotheses and does not assert the two marked residue maps.
- Direct rg of dag/nodes for nodalModelBaseMap/nodalBaseMap found the landed
  `def-trf-universal-nodal-model`. `tools/blueprint_refs.py search 'universal nodal'`
  returned zero blueprint matches; its ancestor command identifies
  `lem-trf-local-term-locality`, consistent with the item's historical ancestry.
- The proposed theorem name was searched in Sheaf, WeilConjectures, and the upstream
  name index; no existing declaration was found.

Source reading: local Stacks curves.tex, 0CBY first proof third paragraph and 0CBX;
more-morphisms.tex, 0GDX statement. This is the finite-type rational split-node subcase,
not a claim that the current blueprint's revised locality proof contains this historical
nodal argument. No statement fault or STATEMENT-DISPUTED flag remains.

Validation: every compilation uses the prescribed scompile.py wrapper in module mode.
The initial chart-only elaboration passed. The delivered signature also explicitly
includes the canonical affine-local identification; its final compile and delivery
preflight results are recorded below.

Final scompile.py run: exit 0; sandbox probe and actual module both compiled;
no errors or warnings. The actual library module compile took 8.0 seconds.

## Second reading by Q07

This is the dispatcher's single worker rereading; no independent worker was started,
as the assignment expressly forbids starting other agents. The maintainer supplies the
independent delivery review. I reopened the JSON statement and final Lean signature and
compared all hypotheses, marked maps and the relative-Spec clause as itemized above.
The initial draft left that last clause in explanatory prose. I repaired it by adding
the actual affine-open, coefficient-and-coordinate-preserving ring equivalences to the
Lean conclusion. This removes that mismatch. I also replaced a proposed fresh owner of
the universal model with the already landed `def-trf-universal-nodal-model` found in the
DAG search. No definition is duplicated, and no strengthening such as affine V, h=0,
a closed base point, or invertibility of h was introduced. All theorem proofs are sorry;
there are no diagnostic commands, auto-bound variables, or file-local constructions.


## Repair of returned delivery 4a9302c9d177

H2 is repaired: the item no longer cites theorem node
`lem-trf-formal-local-structure-nodal-family` in stmt_deps. It cites new definition node
`def-trf-formal-nodal-model-constructions`, existing:true on the unchanged landed module.
The theorem stays in proof_deps. All nine plain declarations are registered, and the
formal-local-structure theorem is excluded. Compared retained delivery fields with the
current main node: only lean and stmt_deps differed. Rebuilt the item record from current
main, retaining its unchanged statement/proof fields and the existing theorem signature.
The delivery wrapper will construct the commit on its refreshed current server base.

## New nodes

`def-trf-formal-nodal-model-constructions` registers the nine existing definitions from
`Sheaf.TraceFormula.FormalLocalStructureNodalFamily`, without moving or copying them.
Its source is Stacks 0CBX/0CBY. Its stmt_deps are definitions of schemes, fibres, residue
fields, affine spectra, adic completion, power series and polynomial rings. The canonical
completed stalk map is described coordinatewise; no conclusion of the formal-structure
theorem is used. The declaration `formalNodalCompletedStalk` represents the record, with
all nine names listed in lean.declarations, existing:true and no file. New searches using
msearch LeanSearch, LeanFinder, and Mathlib grep returned general stalk/completion facts
and no nodal construction. Direct rg found the exact nine constructions in Sheaf, none
in WeilConjectures or the upstream-name index, and no definition owner in dag/nodes.
The search records include the wrapper's original JSON lines. Blueprint search returned
zero matches for formal nodal; the ancestor is lem-trf-local-term-locality.

Repair rereading (same single worker; independent maintainer review follows): opened the
new node beside all nine definitions. Clauses (1)--(9) respectively describe
formalNodalCompletedStalk, formalNodalCoefficientMap, formalNodalFiberCompletionAlgebra,
formalNodalCompletedStalkAlgebra, formalNodalPowerSeriesQuotient, formalNodalModelRing,
formalNodalModel, formalNodalOriginIdeal, and formalNodalModelCompletionAlgebra.
In (8) the ideal is defined for arbitrary h in the completion, exactly as the Lean
definition; no prime-origin or h-in-the-maximal-ideal conclusion is added. Clause (9)
allows every model point o and uses its canonical constant/stalk/completion map. Clause
(4) has no Noetherian assumption: the uniquely determined map of completions exists for
every local stalk map. Empty schemes have no marked point; zero rings, h=0, unit h, and
characteristic 2 are permitted wherever the constructions have their stated arguments.
The four constructions in the item's signature are among these nine. No declaration
uses the formal-local-structure theorem's conclusion. The item module and its signature
remain byte-for-byte those verified by the independent reviewer.
