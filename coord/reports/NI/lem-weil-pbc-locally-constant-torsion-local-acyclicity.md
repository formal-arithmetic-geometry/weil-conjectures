## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyConstantTorsionLocalAcyclicity` states
`AlgebraicGeometry.Etale.isLocallyAcyclicRelative_of_locallyConstant_torsion`, with
only `sorry` as its proof. The source is Stacks Tag 0GJR,
`lemma-locally-acyclic-locally-constant`, read in etale-cohomology.tex.
The declaration docstring retains all seven steps of the DAG proof.

Hypothesis and conclusion correspondence:

- Schemes X and S and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Local acyclicity of f: `(hf : IsLocallyAcyclic f)`, using the recorded
  definition for constant cyclic coefficients at each geometric point.
- Abelian étale sheaf G: `(G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`.
- Locally constant: `[Scheme.IsLocallyConstantSheaf G]`, the recorded existence
  of a jointly surjective étale trivializing cover, with constant restrictions.
- Every geometric point: `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ X)` in `hG`.
- Every element of its stalk: `(m : ((Scheme.pointSmallEtale x).sheafFiber
  (A := AddCommGrpCat.{u + 1})).obj G)`.
  This is precisely the recorded colimit over pointed étale neighbourhoods.
- Torsion, with finite order for each element: `IsOfFinAddOrder m`.
- Order prime to residue characteristic: `(addOrderOf m).Coprime
  (ringChar (X.residueField (x default)))`.
- Characteristic-zero exception: the preceding disjunct
  `ringChar (X.residueField (x default)) = 0`. This is necessary: coprimality
  with zero alone would allow only order one.
- Conclusion: `IsLocallyAcyclicRelative f G`, the recorded predicate requiring
  invertibility of the specified canonical degree-zero map and vanishing of
  all positive cohomology on every strict-local fibre.
- Arbitrary stalk sizes and absence of a uniform annihilator: no `Finite`,
  finite generation, or global integer binder occurs. All order conditions
  are elementwise.

Statement dependencies used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf`:
  `AlgebraicGeometry.Etale.IsLocallyAcyclic` and `IsLocallyAcyclicRelative`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, at
  `Scheme.smallEtaleTopology` with `AddCommGrpCat` coefficients.
- `WeilConjectures.ConstructibleSheaf.Defs`:
  `AlgebraicGeometry.Scheme.IsLocallyConstantSheaf` (and its `LocallyConstantDatum`).
- `Mathlib.CategoryTheory.Sites.Point.Basic`: `Point.sheafFiber`, applied to
  `AlgebraicGeometry.Scheme.pointSmallEtale` from
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `Mathlib.GroupTheory.OrderOfElement`: `IsOfFinAddOrder` and `addOrderOf`.

The module imports all stated proof-dependency modules, including the constant
pullback comparison in ConstructibleSheaf.Defs, strict-henselization functoriality,
strictly henselian sections/stalk, inverse-image germs, constant sections,
finite abelian group structure, global sections, K-injective resolutions and
existence, étale cohomology, affine pullbacks, quasi-separatedness, and the
upstream filtered-colimit theorem. Proof-only imports are non-public.

Edge cases checked: the zero stalk has only an element of order one, prime to
every positive characteristic. Characteristic zero admits every finite order,
while infinite-order elements are excluded by IsOfFinAddOrder even in
characteristic zero. Infinite torsion stalks (for example an infinite direct sum
of allowed cyclic groups) are permitted, with unbounded orders. For the empty
scheme, both the stalk hypotheses and the local-acyclicity conclusion are
vacuous. No finite/nonempty cover index is imposed. Scheme and geometric-point
universes match the dependency definitions and the coefficient universe is u+1.
Every variable and universe is explicitly bound.

Searches for an existing statement:

- msearch LeanFinder: "locally acyclic morphism locally constant torsion etale
  sheaf prime to characteristic": 8 unrelated results, no match.
- msearch Loogle: "IsLocallyAcyclic, IsLocallyConstantSheaf": no hits; unknown
  identifier IsLocallyAcyclic in the Mathlib index.
- msearch grep: "locally.?constant.*[Aa]cyclic|[Aa]cyclic.*locally.?constant":
  zero Mathlib hits.
- msearch LeanSearch: "local acyclicity relative to locally constant torsion
  etale sheaves": unavailable, Internal Server Error; no mathematical verdict.
- rg in WeilConjectures and lean/Sheaf for IsLocallyAcyclic and both orders of
  locally-constant/acyclic: only the dependency definitions and an unrelated
  locally constant cochains module; no existing theorem.
- Search for the item id in upstream WeilConjectures: no match.
- Read the Mathlib order predicates and locally constant datum in upstream
  ConstructibleSheaf.Defs; both are used directly, with no replacement notions.

No new nodes, dependency replacements, node correction, or disputed statement.
The only changed node field is `lean`. Nothing is proved in this delivery.

Validation: scompile.py compiled the delivered file on the server cleanly
(2.9 seconds, nice 19, two threads, 60-second per-file limit). An initial
coefficient-inference error in the stalk-element binder was repaired by explicitly
specifying `(A := AddCommGrpCat.{u + 1})` on `sheafFiber`. No statement changed.

## Second reading by NI

I independently read the node and its seven proof steps, the delivered module,
Stacks etale-cohomology.tex lines 19062–19164 (the section context and definition
0GJP) and lines 19233–19286 (lemma 0GJR and proof). The section assumes only a
morphism of schemes; there is no standing Noetherian, finiteness, smoothness,
properness, or separatedness hypothesis to add. The node agrees with 0GJR.

Object, hypothesis, and conclusion checklist:

- Arbitrary schemes X and S: `{X S : Scheme.{u}}`. PASS. I opened Mathlib's
  Scheme and Scheme.Hom declarations; these are the recorded scheme objects and
  morphisms, with no geometric property imposed.
- Morphism f: `(f : X ⟶ S)`. PASS; no base or auxiliary morphism is substituted.
- Local acyclicity of f: `(hf : IsLocallyAcyclic f)`. PASS. I read the complete
  recorded LocalAcyclicityAbelianSheaf module. Its predicate tests every geometric
  x and every positive cyclic order allowed at that x, including all positive
  orders in characteristic zero, using IsLocallyAcyclicAtRelative.
- Abelian sheaf G on the small étale site of X:
  `(G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`. PASS; the coefficient
  category is abelian groups, with no ring or module structure required.
- Local constancy: `[Scheme.IsLocallyConstantSheaf G]`. PASS. I opened
  ConstructibleSheaf.Defs, including LocallyConstantDatum and the class body.
  The datum is a jointly surjective étale cover with constant localized sheaves;
  it adds neither finite stalks nor a finite cover hypothesis.
- Every geometric point: `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ X)` in hG. PASS; no algebraicity requirement on Ω.
- Every element of the geometric stalk: the following binder m is in
  `((Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G`.
  PASS. I opened pointSmallEtale and Point.sheafFiber: the former has the fibre
  of lifts through étale neighbourhoods, and the latter is the underlying
  presheaf fibre colimit. This is exactly the dependency node's pointed étale
  neighbourhood stalk, rather than a Zariski stalk or sections object.
- Torsion: `IsOfFinAddOrder m`. PASS. Mathlib's predicate means a positive
  natural multiple annihilates m, so the element cannot have infinite order.
- Prime-to-characteristic order: `(addOrderOf m).Coprime
  (ringChar (X.residueField (x default)))`, with preceding disjunct that this
  ring characteristic is zero. PASS. The field at the image point embeds into
  Ω and has the same characteristic; x default is its underlying scheme point.
  The characteristic-zero disjunct retains every finite order, as required.
- Conclusion: `IsLocallyAcyclicRelative f G`. PASS. Expanding the dependency
  predicates quantifies first over every geometric x, then every geometric t
  of the strict localization of S at fx. It asserts IsIso of the specified
  localAcyclicityAlpha and IsZero of the positive-degree étale cohomology of
  the pulled-back G on localAcyclicityFiber. I checked the alpha construction:
  the unique strict-local inverse germ map is followed by restriction and the
  inverse-image composition comparison. Thus both clauses, with the canonical
  map and the same quantifier order, are retained.
- No finiteness of stalks or common annihilator: no Finite instance, global
  annihilator, or uniform bound occurs. PASS.

Edge cases: empty X makes both pointwise hypotheses and conclusion vacuous;
empty S permits only empty X. The zero sheaf has stalk elements of additive
order one, allowed in every characteristic. Characteristic p excludes precisely
orders divisible by p; characteristic zero allows all finite orders but still
excludes infinite order. There is no integer n binder here; in the dependency
local acyclicity definition n=0 is excluded by 0<n, as the node requires.
No index set is introduced, no nonempty or finite cover is demanded, and an
empty trivializing family can cover the empty scheme. Infinite torsion stalks
and unbounded element orders remain allowed. The arbitrary universe u is shared
by schemes and geometric fields, as in the dependency interface, and abelian
coefficients live in u+1. There is no independent smaller test universe and no
unbound variable or universe.

Independent searches (2026-10-15): msearch LeanFinder with "local acyclicity for
locally constant sheaves of torsion abelian groups" returned eight unrelated
condensed-sheaf declarations, no matching theorem. Loogle `IsOfFinAddOrder`
returned the existing element-order predicate and its order/positivity facts;
these confirm the direct use of Mathlib's notion. I ran rg for
`acyclic.*(constant|torsion)|(constant|torsion).*acyclic` across the full upstream
WeilConjectures and project lean/Sheaf, and for `local.?acycl` and related word
orders across upstream SixFunctors, project AlgebraicGeometry and Mathlib
AlgebraicGeometry. Hits were the local-acyclicity dependency and unrelated
injective, affine-local, or topological acyclicity results. None states 0GJR.
No duplicate definition or existing matching theorem was found.

There are no new definition nodes or dependency modules to review and no
statement_change. I checked the docstring against all seven DAG proof steps:
trivialization compatible with germs, finite-subgroup colimit, cyclic
structure, cyclic local acyclicity, finite sums via resolutions, qcqs filtered
colimits, and the canonical degree-zero map and positive vanishing. All are
present. The sole declaration has proof `by sorry`, no definitions or hidden
proofs are added, and no private notation or local instances occur. Its recorded
lean.statement is verbatim equal to the signature in the file (checked by exact
string comparison). No mismatch was found; the Lean and node are unchanged.
The second reading adds only this independent review report.
