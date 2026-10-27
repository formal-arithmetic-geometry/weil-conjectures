## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeTangentWeightBaseChange` states
`AlgebraicGeometry.RelativeTangentWeights.exists_data`. There is exactly one postponed
proof, `exists_data`; its docstring carries all twelve proof steps of the node. No
mathematical statement is corrected. This repair adds one definition ownership node,
`def-sfb-split-torus-comodule-weights`, reusing two existing definitions; no
dependency module is needed.
The same-node helper definitions construct actual maps and subtypes; none chooses
unspecified data or contains sorry. `Data` is an explicit package of conclusions,
not an extra hypothesis.

Hypothesis and clause correspondence:

- A nonzero commutative Noetherian ring: `{A : Type u} [CommRing A]`, then
  `[Nontrivial A] [IsNoetherianRing A]` on `exists_data`.
- X = Spec A: the base category is `Over (Spec (.of A))` throughout.
- r >= 0 and M = Z^r: `r : ℕ`; the character type is
  `ULift.{u} (Fin r → ℤ)`. ULift only puts this same lattice in Type u, needed
  by the existing Hopf-spectrum construction. Its additive group is the pointwise
  integer group. Rank zero gives one character, not an empty character set.
- T = Spec A[M], multiplication of units, and the characters e^m: the recorded
  `ringDiagonalizableGroup A (ULift (Fin r → ℤ))` uses Mathlib's canonical
  `AddMonoidAlgebra` Hopf structure, with coproduct e^m tensor e^m and counit 1.
  `torusPoint f` is exactly `Spec.map f` over Spec A. Evaluation of the basis
  element `AddMonoidAlgebra.single m 1` is the character chi_m. No extra
  character or torus structure is assumed.
- G an A-group scheme: `G : Grp (Over (Spec (.of A)))`, using the recorded
  `CategoryTheory.GrpObj` construction, whose fields are the associativity,
  unit, and inverse diagrams.
- Smooth affine finite type: `[Smooth G.X.hom] [IsAffine G.X.left]`, and
  `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]` as the finite-type
  conjunction recorded by def-weil-finite-type-morphism. Over the affine base,
  `IsAffine G.X.left` is the affine group-scheme condition.
- Action by group automorphisms: `a : ModObj T.X G.X` is the actual scheme
  action, including its unit and associativity diagrams. `act a t x` composes
  the pair (t,x) with this action map. `hgroup` says it preserves multiplication
  for every algebra B and all t,x,y. The action of t is invertible with inverse
  the action of t inverse; multiplication preservation therefore says precisely
  group automorphism, without any extra faithfulness hypothesis.
- g = ker(G(A[epsilon]) -> G(A)): use the already constructed `GrpObj.Lie G.X`.
  In `Lie.Ring`, `tangentGroup G.X` is exactly this kernel;
  `GrpObj.infPointsEquivTangentGroup` and `GrpObj.lieEquiv` give its canonical
  bijection with Lie, and `GrpObj.tangentPoint` is that map on points.
  `Data.normalize` fixes our comparison to this existing point, so this does
  not replace the kernel by an unrelated module. `Data.E A` is the asserted
  comparison with this precise kernel.
- The specified addition and scalar multiplication: `Data.add` is kernel-point
  multiplication; `zero` and `neg` give its identity and inverse; `scale` uses
  precisely `DualNumber.scale b` (epsilon maps to b epsilon). Thus the E B
  bijections are B-linear for the intrinsic kernel module operations, rather
  than arbitrary set bijections. A separate duplicate module instance on this
  equivalent kernel subtype would add no content and is not introduced.
- Finite projectivity of g: `Data.finite` and `Data.projective` are
  `Module.Finite A (GrpObj.Lie G.X)` and `Module.Projective A ...`.
  Mathlib `Module.Finite.exists_comp_eq_id_of_projective` identifies this
  precisely with a summand of a finite free module; no local freeness chosen.
- Differentiated A-linear coaction: `Data.rho` is the required A-linear tensor
  map. `coassoc` and `counit` are the two actual coalgebra identities.
  `evaluatedAction rho f` extends the evaluation of rho B-linearly, by
  b tensor v mapping to b times flip((1 tensor f)rho(v)).
  `Data.differentiated` identifies its action on EVERY extended tangent vector
  with the actual given scheme action at EVERY algebra-valued torus point.
  In particular B=A[M], f=id recovers rho uniquely from the generic action;
  it cannot be an arbitrary coaction unrelated to a.
- g_m = {v : rho(v)=v tensor e^m}: the existing `SplitTorus.weightSpace rho m`
  is the kernel of exactly rho minus that pure-tensor linear map.
- g = direct sum of its weights: `Data.decomposition` says the actual
  `DirectSum.coeLinearMap` of inclusions is bijective. That map is A-linear,
  so this states the required module isomorphism with its specified inclusions.
- Finite support: `Data.support` is `Set.Finite {m | weightSpace rho m ≠ ⊥}`.
- Every summand finite projective: `Data.weight_projective m` gives both
  `Module.Finite` and `Module.Projective`, also when that summand is zero.
- EVERY commutative A-algebra B: all `Data` fields quantify B : Type u with
  `[CommRing B] [Algebra A B]`; there is no nonzero, Noetherian, reducedness,
  flatness, or finite-type requirement on B.
- The natural B-linear tangent comparison: `E B : B tensor_A Lie ≃ Kernel G B`
  together with its add, zero, neg, scale, normalize and natural fields.
  `Kernel G B` consists of morphisms Spec(B[epsilon]) -> G over A reducing
  to the identity. By the defining universal property of G_B, these are exactly
  morphisms to G_B over B reducing to its identity. The equivalent points
  description avoids introducing or choosing a second pullback group object.
  `normalize` and `natural` force the map on 1 tensor v to be the actual
  scalar-extended tangent point; `scale` forces b tensor v to be its b multiple,
  and `add` forces the comparison on the whole tensor product.
- Exact weight comparison for the FULL T_B coaction: `weight_baseChange` says
  the natural tensor inclusion of each weight is injective and its range,
  `(weightSpace rho m).baseChange B`, equals the full weight space of
  `SplitTorus.baseChangeCoaction B rho`. The latter uses the canonical
  B tensor A[M] = B[M] isomorphism. `differentiated` on all extended vectors
  and all f:A[M]->B identifies this with the full differentiated T_B action
  transported through E B. Thus the image in the actual tangent kernel is
  exactly its full m-weight submodule, including nonflat B.
- Successive extensions: `Data.natural` holds on every tensor vector and every
  algebra map h:B->C. On b tensor v it is precisely the tower formula
  1 tensor h(b) tensor v, which after multiplying the C factor is
  c h(b) tensor v. B-linearity extends E B to C tensor_B its target, and this
  formula says its composite with the canonical reassociation is E C.
  The natural tensor weight inclusions obey the same formula, so the identity
  also restricts to every weight. No arbitrary-lift or identity case is omitted.
- No reductivity, connectedness, localness or residue-characteristic restriction:
  none occurs in the theorem's binders. The Noetherian and nonzero restrictions
  on A are precisely those of the node, not restrictions on test B.

Dependency declarations read and used:

- def-weil-pbc-noetherian-ring: Mathlib.RingTheory.Noetherian.Defs,
  `IsNoetherianRing` (all ideals finitely generated).
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Spec`, `Spec.map` (contravariant ring maps).
- def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp,
  `CategoryTheory.GrpObj` and `Grp`; general base accepted by this interface.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  `AlgebraicGeometry.Smooth`, the recorded affine-local definition.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType
  and QuasiCompact, `LocallyOfFiniteType` and `QuasiCompact`.
- def-weil-pbc-module-tensor-product: Mathlib.LinearAlgebra.TensorProduct.Defs,
  `TensorProduct`; Basic.lift and Map.rTensor are inherited via imports.
- def-weil-pbc-direct-sum-modules: Mathlib.Algebra.DirectSum.Module,
  `DirectSum`, its module instance, and `DirectSum.coeLinearMap`.
- def-weil-module-base-change: Mathlib.LinearAlgebra.TensorProduct.Tower,
  `LinearMap.baseChange` and `Submodule.baseChange`, with the Mathlib order
  B tensor_A g canonically equivalent to the node's opposite tensor order.
- Added already-landed statement dependencies: def-sfb-ring-diagonalizable-group,
  Sheaf.AlgebraicGeometry.RingDiagonalizableGroup,
  `AlgebraicGeometry.ringDiagonalizableGroup`; def-sfb-split-torus-comodule-weights,
  Sheaf.RepresentationTheory.RelativeTorusBundleWeights, `SplitTorus.weightSpace`
  and `SplitTorus.baseChangeCoaction`; def-wf-lie-algebra-derivation owns the
  existing `GrpObj.Lie` construction, used through the smaller
  WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring module. The latter's
  Lie.Basic, Lie.InfPointsEquiv and Lie.Functoriality source and docstrings were
  read: Lie = Hom(e*Omega,O), tangentPoint = the canonical dual-number point.
  This existing definition itself accepts arbitrary ring bases; no field-only
  differential theorem or matrix Lie algebra is used.
- All already-stated proof dependencies are imported non-publicly:
  Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties (`Spec_iff`),
  Mathlib.RingTheory.Smooth.Basic (`Algebra.Smooth`),
  Mathlib.RingTheory.Kaehler.TensorProduct (also imports Kaehler.Basic;
  `KaehlerDifferential`, `D`, `linearMapEquivDerivation`,
  `tensorKaehlerEquivBase`), Mathlib.RingTheory.TensorProduct.Maps
  (`Algebra.TensorProduct.productMap`, importing its canonical tensor algebra),
  and Mathlib.LinearAlgebra.Dual.Lemmas (`Module.dual_projective`,
  `Module.dual_finite`). The existing lemma node
  lem-sfb-group-algebra-coaction-grading has no Lean binding yet, so no
  fictional import is added; its coefficient argument remains in the proof
  docstring. It is a proof prerequisite, not missing statement data.

Searches:

1. msearch.py leansearch, query "relative tangent module smooth group scheme Lie
   finite projective base change": eight hits, including
   `KaehlerDifferential.tensorKaehlerEquivBase`, general smooth base change and
   LieModule base change; none gives this group-scheme statement.
2. msearch.py leanfinder, query "Smooth affine group scheme tangent Lie module
   torus weight decomposition arbitrary base change": eight hits, beginning
   with LieModule.weightSpaceOfIsLieTower, LieAlgebra.rootSpaceWeightSpaceProduct
   and LieModule.instLinearWeightsOfIsLieAbelian; these concern Lie algebra
   weights, not torus group-scheme coactions. No exact statement found.
3. msearch.py loogle, query "DualNumber, GrpObj, TensorProduct": zero hits,
   unknown unqualified GrpObj. Direct Mathlib source inspection found the
   qualified `CategoryTheory.GrpObj` and no relative tangent theorem.
4. msearch.py grep, query "tangent|Tangent|DualNumber", AlgebraicGeometry:
   nine unrelated elliptic tangent and cotangent import/property hits.
5. rg searches over lean/WeilConjectures and lean/Sheaf for tangent, Tangent,
   DualNumber, group-scheme Lie, weightSpace, baseChangeCoaction and the item id:
   found the general-ring Lie and tangent-point constructions and the landed
   bundle-weight module, which are reused. The field-only affine dual-number
   calculus is not applicable to an arbitrary Noetherian A and is not copied.
   No exact statement of this node is present. The requested item-id search
   in WeilConjectures also gives no match.
6. tools/blueprint_refs.py search "relative tangent" gave the diagonal regular
   immersion and smooth relative tangent nodes, not this group-action result.
   The newest blueprint unit _section.md was read, and the inherited ancestor
   command returns None; no new blueprint provenance is manufactured.

Source checked: Conrad PDF, printed p.2 for dual-number Lie functor, Section 4
introduction, printed p.107, and the matching weight/base-change discussion on
printed p.99 (PDF page index 98). Existing stage-1 proof is preserved verbatim
in the node; its elementary calculations supply the general smooth-group
version, as already noted by the source and proof_origin records.

Edge cases: r=0 (only the trivial character); G with zero Lie module; the zero
weight and absent weights; nonflat B=A/I; B the zero ring (all modules/kernels
collapse to their singleton); disconnected A with varying ranks; additive G
acted on via a character divisible by residue characteristic. No coefficient
comparison is made only at field points, so inseparability and small
characteristic cause no omitted case. Finite projective does not mean globally
free, and no basis, local ring or constant rank is assumed.

Validation: scompile.py compiled this file both in its private sandbox context
and at its proper module name, cleanly (7.3s and 6.6s); deliver2.py --no-push
also returned OK, verifying the records, preflight and compilation. The sole
proof is sorry as required by stage 2. Variables and universes are explicitly
bound, with autoImplicit and relaxedAutoImplicit disabled.

## Second reading by Q87

A separate pass through the original node and final source checked all clauses
against the correspondence above. This is a self-review; the dispatcher forbids
starting other agents and the maintainer supplies the independent review.
The first draft characterized differentiation only on the vectors 1 tensor v.
The final version strengthens that defining characterization to every vector
of B tensor_A Lie using the constructed B-linear evaluatedAction, so it exposes
the full base-changed torus action directly. All geometric assumptions remain
in exists_data, not in Data or in test-algebra binders. The coaction, kernel,
weight inclusions and tensor comparisons were checked against their actual
source definitions. No statement mismatch or mathematical dispute remains.


## New nodes

`def-sfb-split-torus-comodule-weights` owns precisely the existing plain definitions
`SplitTorus.weightSpace` and `SplitTorus.baseChangeCoaction` in
`Sheaf.RepresentationTheory.RelativeTorusBundleWeights`, with `existing: true`.
No new Lean module or declaration is introduced. Its primary Lean signature is
copied verbatim from the existing `noncomputable def weightSpace` declaration.
The source is Conrad, Proposition 3.1.9 proof (1), printed p.86. The new node
states the underlying constructions on arbitrary modules: the kernel of rho
minus tensor with e^m, and the composite of scalar extension, tensor distribution
and B tensor A[M] = B[M]. The existing `baseChangeCoaction` definition was read
in full and has exactly that composite. No finite-generation, projectivity,
coaction-identity, flatness or nonzero-ring assumption is needed to define them.
The item cites this new node instead of the theorem node.

Searches for the new node are included verbatim in its `mathlib_searches`:
LeanSearch for split-torus comodule weight submodules and coaction base change;
LeanFinder for the kernel and scalar-extension constructions; msearch grep for
weightSpace/baseChangeCoaction in Mathlib RepresentationTheory; and direct rg
of upstream RepresentationTheory and the existing project module. Mathlib's
Lie weights, abstract representation submodules and Submodule.baseChange do
not define this pair of coaction constructions. The exact project definitions
are reused. DAG search for the names finds only the existing theorem node,
which does not own a definition node; tools/blueprint_refs.py search "comodule
weights" finds zero blueprint nodes. The field-only
`def-sfb-torus-character-tangent-weights` is about field-valued character points,
not arbitrary-ring full-coaction kernels, so it cannot own these constructions.
The new definition's three dependencies supply the group algebra, tensor
product and scalar extension; they are exactly the three citations in its text.
Its provenance retains the ancestor command's inherited null result and prepends
the item to the inherited via chain. `import_flags: []` records reachability
through the item.

New-node clause and edge-case check: A is any commutative ring, M any additive
abelian group, V any A-module and rho any A-linear map, matching the general
universes and binders of the existing definitions. The formula for weightSpace
is the kernel printed in the source. The baseChangeCoaction formula agrees
factor by factor with the existing source. In particular it needs no flatness
or finite projectivity. A=0, B=0, V=0, an absent weight, a trivial lattice and
nonflat B are all admitted by these definitions. No theorem is asserted by the
new node and neither definition is selected from a postponed theorem.

## Repair of returned delivery d0f63ca1ea5b

H2 is repaired by creating `def-sfb-split-torus-comodule-weights` with the exact
existing declarations, then replacing `lem-sfb-relative-torus-bundle-weights`
by this definition node in the item's `stmt_deps`. The bundle-weight theorem
remains available as a proof input through the existing module import; no theorem
is used as the owner of plain definition data. The original accepted proof graph
and proof text are preserved, as are the mathematical statement and Lean module.
No proof dependency is promoted into a statement dependency. The other two
previously added statement dependencies remain the actual definition nodes for
the torus and Lie module.

Compared the retained delivery with current main: only `lean` and `stmt_deps`
differed before repair. Current main still has no Lean attachment for the item.
The original module SHA256 remains
`299d1a2e7adcdfdd09c5a24d0447533e9eb390c416be2aae455dfa132aee3ac7`.
The deliver2 wrapper rebases this repaired sandbox onto current main; no direct
Git mutation or live-source edit is performed.

Repair second reading: the two helper docstrings and full bodies were re-read,
as were the new node, the item dependency list and the unchanged theorem source.
The only returned defect was helper ownership, now supplied by the definition
node. The clause-by-clause mathematical mapping above remains applicable and
matches the maintainer's independent review. The retained module was compiled
again with scompile.py, cleanly in the sandbox and at its proper module name
(7.3s and 6.6s). No new file needs compiling because the ownership node records
existing declarations in the already imported module.
