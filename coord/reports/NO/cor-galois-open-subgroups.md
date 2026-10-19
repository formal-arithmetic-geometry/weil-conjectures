## Worker report

The module `Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups` states
`AlgebraicGeometry.Scheme.FiniteEtale.connected_cover_open_subgroups`, with `sorry`.
No new definitions, new nodes, dependency modules, or statement corrections are needed.
The corrected stage-1 statement is retained exactly.

Hypotheses and clauses:
- A connected base is `{Y : Scheme.{u}} [ConnectedSpace Y]`. Mathlib's
  `ConnectedSpace` includes nonemptiness and preconnectedness; its equivalence to
  the clopen criterion is `connectedSpace_iff_clopen`.
- The geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
  and `s : Spec (.of Ω) ⟶ Y`. This is the usual algebraically closed geometric
  point, with no restriction on its characteristic or residue-field extension.
- The group is literally `Aut (fiber s)`, with Mathlib's natural evaluation action
  and topology induced from all finite discrete permutation groups. The established
  finite-étale/FLC equivalence identifies this with the sheaf-fibre automorphism
  group in the node. No arbitrary group or additional action is assumed.
- Covers are the recorded `Y.FiniteEtale`, and connected nonempty total spaces
  are `ConnectedSpace P.obj.left` (nonemptiness is part of this predicate).
  Marked points are `p : (fiber s).obj P`.
- The first conjunct, universally for every such P and every marked p, asserts
  openness of `MulAction.stabilizer (Aut (fiber s)) p` and
  `P.obj.hom.IsFiniteLocallyFreeOfDegree (MulAction.stabilizer ... p).index`.
  The latter is the recorded constant fibre-rank degree notion, not a replacement
  degree defined only as cardinality. This renders the degree assertion in both forms.
- The second conjunct realizes EVERY open subgroup H by a connected cover and a
  marked point whose stabilizer equals H: surjectivity of the pointed assignment.
- The third conjunct says that a pointed isomorphism exists exactly when the two
  stabilizers are equal. The marking condition is `(fiber s).map e.hom p = q`.
  Together with the second conjunct this states a bijection on pointed isomorphism
  classes; it does not claim uniqueness of a representative or choose one.
- The fourth conjunct says that `Nonempty (P ≅ Q)` holds exactly when the two
  stabilizers are conjugate. Its formula is
  `∀ h, h ∈ Stab(p) ↔ g⁻¹ * h * g ∈ Stab(q)`, equivalently
  `Stab(p) = g Stab(q) g⁻¹`. Taking P = Q and the identity isomorphism proves
  independence of the chosen marked point. Together with realization of H this
  is exactly the well-defined unpointed bijection onto conjugacy classes.
  No quotient types or additional classification definitions are required to
  state these exact surjectivity and equivalence-relation criteria.

Dependency declarations read and used:
- `Mathlib.Topology.Connected.Basic`, `ConnectedSpace`, lines 703–709;
  `Mathlib.Topology.Connected.Clopen`, `connectedSpace_iff_clopen`, lines 710–713.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`,
  `AlgebraicGeometry.Scheme.FiniteEtale` and `.FiniteEtale.fiber`, including its
  docstring and signature (lines 80–81 and 109–115). Fibres are finite sets of
  lifts of s and morphisms act by composition. The recorded dependency provides
  precisely the finite-étale side needed here.
- `Sheaf.AlgebraicGeometry.GaloisCategories`, `AlgebraicGeometry.Scheme.FLC`:
  finite locally constant sheaves; imported as the node's category dependency.
  This node explicitly reuses the upstream finite-étale category and fibre.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` and
  `.IsFiniteLocallyFreeOfDegree`, lines 778–791. The latter includes the former
  and constant `fiberDegree_eq` for every point of the base.
- Mathlib `CategoryTheory.PreGaloisCategory` supplies the evaluation action
  on `Aut (fiber s)` (Galois/Basic.lean:192–203) and its induced topology
  (Galois/Topology.lean, `autEmbedding` and the `TopologicalSpace (Aut F)` instance).
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic` supplies the Galois
  category/fibre functor instances and explains this literal automorphism group.
- Proof-only imports are the recorded modules of `thm-galois-fundamental`,
  `lem-galois-finite-etale-connected-object`,
  `lem-galois-coproduct-copies-morphisms-clopen`, and
  `lem-weil-pbc-finite-locally-free-degree-locally-constant`. The geometric-fibre
  theorem is in the already public FiberDegree module, and the étale and abstract
  connected-object notions are already imported through the public dependencies.
  The declaration docstring carries all six DAG proof steps and names their inputs.

Edge cases checked before writing:
- The empty base and empty total cover are excluded exactly by ConnectedSpace,
  as the statement requires; an arbitrary finite étale cover is not assumed connected.
- Over an algebraically closed point, the group is trivial and the only connected
  cover has degree one; the whole subgroup and index-one case are included.
- Non-normal open subgroups are included. No normality or Galois-cover hypothesis
  is imposed, and the conjugacy direction is explicitly checked.
- All choices of p and q are quantified, so changing a marked point is covered.
- No positive-characteristic, zero-characteristic, or finite-type assumption on Y
  is introduced. The universe u is arbitrary and the literal automorphism group
  is allowed to live one universe above the covers, as in the upstream API.

Searches actually run:
- msearch leanfinder: "connected finite etale covers classified by conjugacy classes
  of open subgroups of fundamental group". Eight hits, including
  `instIsPretransitiveCarrierObjFintypeCatOfIsConnected`,
  `exists_hom_from_galois_of_connected`,
  `exists_set_ker_evaluation_subset_of_isOpen`, and
  `instIsFundamentalGroupAutFunctorFintypeCat`. These are abstract ingredients,
  not the scheme classification together with the degree assertion.
- msearch loogle: `"stabilizer"`. Twelve hits, including `MulAction.stabilizer`
  and its membership lemma; no exact classification statement.
- msearch leansearch: "connected finite etale covers open subgroups classification".
  Service unavailable: Internal Server Error; not recorded as a negative match.
- msearch grep: `open_subgroup|openSubgroup|stabilizer` in CategoryTheory/Galois.
  Twenty-two hits; `isoQuotientStabilizerOfIsConnected` and abstract open-coset
  construction facts do not supply this full scheme statement.
- rg of upstream WeilConjectures for the exact node id: no match.
  rg of its FundamentalGroup directory for open-subgroup names and
  stabilizer/index: no full classification declaration.
- rg of lean/Sheaf/AlgebraicGeometry for the same concepts: image-stabilizer,
  open-index and fibre-equivalence statements, none asserting both classifications.
- rg of dag/lean_names_upstream.json for stabilizer/open-subgroup names:
  only `lem-wf-stabilizer-density`, not this statement.

Validation: scompile.py compiled the delivered module on the server in 1.6 seconds,
with nice 19, two threads, a 60-second limit, and no compiler diagnostics.

## Second reading by NO

I independently opened the delivered node and OpenSubgroups.lean, the blueprint
source cor-galois-open-subgroups.md, and Stacks pione.tex at
`definition-G-set-continuous`, `proposition-galois`,
`lemma-finite-etale-connected-galois-category`, and `theorem-fundamental-group`.
I also read morphisms.tex at `definition-finite-locally-free`, `lemma-finite-flat`,
and `lemma-finite-locally-free`. The Stacks hypotheses are an arbitrary connected
scheme and a geometric point; there is no Noetherian or characteristic hypothesis.
The older blueprint wording incorrectly identifies unpointed covers with individual
subgroups. The BASE DAG already corrects this to conjugacy classes, with individual
subgroups classifying pointed covers. The delivery changes only `lean`, not the
statement, and needs no new statement correction or citer verdicts.

Object/hypothesis/conclusion checklist, in the order of the node:

1. Connected base Y: `{Y : Scheme.{u}} [ConnectedSpace Y]`. PASS.
   I read `ConnectedSpace` in Mathlib/Topology/Connected/Basic.lean and
   `connectedSpace_iff_clopen` in Clopen.lean: nonemptiness and the clopen
   criterion agree exactly with def-weil-connected-scheme.
2. Geometric point: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
   and `(s : Spec (.of Ω) ⟶ Y)`. PASS. This is a geometric point with arbitrary
   algebraically closed field, with no chosen rational point of Y required.
3. Group G and its action/topology: literally `Aut (fiber s)` throughout. PASS.
   I read `FiniteEtale.fiber` in the recorded upstream FiniteEtale module:
   objects are finite sets of lifts of s, maps compose the lift with the
   Y-morphism. Mathlib Galois/Basic.lean's action is `σ.hom.app X x`;
   Galois/Topology.lean's `autEmbedding` and TopologicalSpace instance give
   the evaluation-induced topology from finite discrete automorphism groups.
   This is the node's recorded finite-étale model of the fundamental group.
   I also read `exists_fiber_flc_equivalence` in the proof dependency module:
   its natural fibre identification and continuous group identification
   provide the FLC interpretation. No arbitrary action or extra group is assumed.
4. Covers P: `(P : Y.FiniteEtale)` and `ConnectedSpace P.obj.left`. PASS.
   I read the actual upstream `Scheme.FiniteEtale` abbreviation: it is the
   full subcategory of Y.Etale on finite structural morphisms. Thus the
   cover is finite étale over Y, and its total space is connected and nonempty.
   GaloisCategories.lean explicitly reuses this category and defines only FLC.
5. Marking: `p : (fiber s).obj P`. PASS. A marked isomorphism is exactly
   `∃ e : P ≅ Q, (fiber s).map e.hom p = q`; the isomorphism is over Y,
   because it belongs to the full subcategory of the category over Y.
6. Assignment lands in open subgroups: first conjunct, for every connected
   cover and every marking, `IsOpen (MulAction.stabilizer ... p : Set ...)`.
   PASS. Neither normality nor a Galois-cover condition is imposed.
7. Degree/index: the other half of that same conjunct is
   `P.obj.hom.IsFiniteLocallyFreeOfDegree (MulAction.stabilizer ... p).index`.
   PASS. I read both classes in upstream FiberDegree.lean: the former
   extends finite, flat, locally of finite presentation, and degree d
   asserts `fiberDegree s = d` at every base point. This is constant rank,
   rather than a new definition by counting this single geometric fibre.
8. Pointed bijection, surjectivity: second conjunct quantifies over EVERY
   `H : Subgroup (Aut (fiber s))` with `IsOpen H` and produces connected P
   and p with stabilizer EQUAL to H. PASS; no finite-index hypothesis added.
9. Pointed bijection, injectivity on classes: third conjunct equates pointed
   isomorphism existence with equality of stabilizers for all P,Q,p,q. PASS.
   Together with item 8 this is exactly the asserted pointed classification.
10. Unpointed well-defined bijection: fourth conjunct equates `Nonempty (P ≅ Q)`
    with `∃ g, ∀ h, h ∈ Stab(p) ↔ g⁻¹ * h * g ∈ Stab(q)`.
    PASS. The displayed condition is `Stab(p) = g Stab(q) g⁻¹`, hence precisely
    conjugacy. Taking P=Q gives independence of the marking; item 8 gives
    surjectivity on conjugacy classes. Nonempty connected covers have markings
    by upstream `nonempty_fiber_of_nonempty`, which I opened; thus quantifying
    over p,q does not omit an unmarked cover. No representative uniqueness or
    stronger morphism classification is asserted.

Edge cases: the empty scheme and empty cover are excluded exactly by the node's
connectedness convention. A whole subgroup is included (index one); non-normal
open subgroups are included; all markings and both conjugacy directions are
covered. The trivial fundamental group and degree-one cover are included.
Degree zero is not an extra excluded numerical case: a nonempty connected cover
has nonempty geometric fibre and hence positive degree. There is no index set
or integer n in this statement. All characteristics and non-Noetherian bases
are allowed. The universe u is arbitrary, shared by the geometric point and
schemes as in the recorded fibre functor; Aut may live at u+1. There is no
independent smaller test-object universe or hidden small-group hypothesis.

Independent H4 searches (different queries from the first writer):
- msearch leanfinder: `pointed connected finite étale covers classification
  stabilizer index fundamental group`. Eight hits, including
  `fiberIsoQuotientStabilizer`, `exists_set_ker_evaluation_subset_of_isOpen`,
  and `isPretransitive_of_isConnected`. I opened fiberIsoQuotientStabilizer
  in Mathlib/CategoryTheory/Galois/EssSurj.lean: it identifies one connected
  fibre with its stabilizer quotient, not the scheme classifications or degree.
- msearch loogle: `"isoQuotientStabilizer"`. Two hits: that abstract result
  and `FintypeCat.isoQuotientStabilizerOfIsConnected`; neither is this statement.
- msearch grep: `fiberIsoQuotientStabilizer|quotient_finite_of_isOpen|index_stabilizer`.
  Twenty-one hits: coset finiteness and orbit/index ingredients, no exact match.
- msearch leansearch: `pointed connected finite etale covers bijection open subgroups`.
  Service unavailable (Internal Server Error); no negative conclusion drawn.
- Direct rg over upstream WeilConjectures, project lean/Sheaf, and Mathlib's
  Galois modules for `conjugacy.*(cover|subgroup)|classif.*(cover|subgroup)|pointed.*cover`,
  plus open-subgroup/stabilizer/index searches in both FundamentalGroup directories.
  The existing ImageStabilizerOpenIndex declaration gives openness and fibre
  cardinality for a separately supplied fundamental group; it gives neither
  classification nor finite locally free degree. No full matching declaration.
- Direct rg for the proposed declaration in Mathlib, WeilConjectures,
  lean/Sheaf, and dag/lean_names_upstream.json found no name collision.

H5/H6/H8/H9: the delivery has one theorem with proof `sorry`, no definitions,
no new nodes, and no dependency modules. The six docstring proof steps match
all six DAG proof steps, including connectedness in both directions, cosets,
realization, pointed/unpointed classification, and constant rank. Source places
and blueprint tags are present. All Lean lines are at most 100 characters;
there is no file-local notation, private copy, local instance, hidden let/show,
unbound variable, or unbound universe. The node's `lean.statement` equals the
file's theorem signature verbatim (checked mechanically).

Mismatches found: none. Changes: appended this independent second reading only;
the correct theorem, node record, and Worker report were retained.

Second-reader validation: scompile.py compiled the sole delivered module on the
server in 1.7 seconds, nice 19, two threads, 60 seconds per file, with no diagnostics.
