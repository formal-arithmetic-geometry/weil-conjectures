## Worker report

The delivery states `HopfAction.rationalLinearHom` in
`Sheaf.RepresentationTheory.RationalLinearHom`. Its only theorem proof is `sorry`.
The helper `HopfAction.coactionPointAction` is real data: the tensor universal
property extends the evaluated coaction A-linearly. It is a canonical map belonging
to this node's stated action formula, allowed by the missing-helper rule; it is not
an arbitrary action or a chosen map from an existence theorem.

Sources read: Milne, Algebraic Groups (2017), Remark 4.1 and equations (24)--(25),
printed pp.83--84 (PDF pp.95--96); and Lemma 22.40 (b) to (a), printed p.477
(PDF p.489). The former identifies natural actions with coordinate coactions and
uses all algebra-valued points. The latter gives the exact conjugation formula and
identifies fixed maps with G-homomorphisms. Its additional character hypothesis is
used later for a fixed line, not for this Hom construction. The accepted node's
proof via unrestricted Hopf linearization supplies rationality without finite type.

Clause-by-clause translation:

- A field k is `(k : Type u) [Field k]`, including arbitrary characteristic.
- A group scheme over k is `(G : Scheme.{u}) [G.Over (Spec (.of k))]
  [GrpObj (G.asOver (Spec (.of k)))]`. Affineness is `[IsAffine G]`.
- C = k[G] is exactly `Γ(G, ⊤)`. The imported canonical instance
  `HopfAction.coordinateHopfAlgebra` supplies its comultiplication, counit and
  antipode from the actual group scheme. No unrelated Hopf algebra is supplied.
  The affine identification with Spec C is the existing `G.isoSpec`; the
  statement works directly with C, so no new affine-spectrum construction occurs.
- V and W are arbitrary-universe types with `[AddCommGroup] [Module k]` and
  `[FiniteDimensional k]`. Both finite-dimensional hypotheses are retained.
- Their rational structures are the two linear maps `ρV`, `ρW`. Their four
  assumptions `hVcoassoc`, `hVcounit`, `hWcoassoc`, `hWcounit` use the existing
  `HopfAction.Coassociative` and `HopfAction.Counital`. These predicates say exactly
  the two equations in the node, with the tensor associator and right unitor
  made explicit by their definitions.
- H is the actual type `V →ₗ[k] W`. The existential `ρH` is a k-linear map from H
  to H tensor C, and the first two conjuncts impose its coassociativity and counit.
  Thus this is a rational coaction, not just an abstract group action.
- For every commutative k-algebra extension, the binders are
  `(A : Type (max u t)) [CommRing A] [Algebra k A]`. The free universe t admits
  arbitrarily large algebras; using max ensures the tests include the coordinate
  algebra, with universe lift if necessary. There is no nonzero or domain condition
  on A. In particular the zero algebra is included.
- Mathlib's scalar extension uses A tensor M, rather than the node's M tensor A.
  These are related by `TensorProduct.comm`; this is already the convention in the
  dependency `def-weil-module-base-change`. The point-action helper includes the
  symmetry explicitly, rather than treating right and left tensors as equal.
- `j : A ⊗[k] (V →ₗ[k] W) ≃ₗ[A] (A ⊗[k] V →ₗ[A] A ⊗[k] W)` is the displayed
  Hom base-change identification. The condition
  `j (a ⊗ₜ[k] f) = a • f.baseChange A` fixes it on every tensor generator.
  Consequently it is exactly the canonical map, uniquely specified, with genuine
  inverse supplied by its `LinearEquiv` type. Its action on b tensor v is
  (a*b) tensor f(v), after tensor symmetry. No arbitrary comparison is allowed.
- For affine G, an A-point is equivalently `(g : Γ(G, ⊤) →ₐ[k] A)`, by the affine
  Spec dictionary. The inverse point is the composite with
  `HopfAlgebra.antipodeAlgHom k Γ(G, ⊤)`, using the canonical coordinate Hopf
  instance. This keeps all A-points, including nilpotent ones.
- `coactionPointAction k C M A ρ g` is built by applying `g` to the C factor of
  ρ, switching M tensor A to A tensor M, and extending A-linearly. Thus it is
  precisely the action induced by that coaction. The formula quantified over
  `g`, `F : A ⊗[k] H`, and `x : A ⊗[k] V` states
  j(g.F)(x) = g.(j(F)(g^-1.x)). The action laws themselves are encoded by the
  coaction axioms, as in the node's definition of rational module.
- For every `f : V →ₗ[k] W`, the first final biconditional identifies
  `ρH f = f ⊗ₜ[k] 1` with
  `ρW ∘ₗ f = f.rTensor Γ(G, ⊤) ∘ₗ ρV`, exactly the coaction square.
- The second final biconditional identifies this same square with
  `f.baseChange A (g.x) = g.(f.baseChange A x)` for every A, g and x. This is the
  node's final equivalence, on all extended vectors rather than only generators.
- There are no hypotheses of finite type, smoothness, reducedness, characteristic
  zero, connectedness or algebraic closedness. No statement correction is needed.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, read at line 180.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  Mathlib.CategoryTheory.Monoidal.Grp, including its inversion and two inverse laws;
  its specialization to the over-category was read in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  Mathlib.LinearAlgebra.TensorProduct.Defs; `TensorProduct.lift`, Basic;
  `LinearMap.rTensor`, Map. Their full definitions and generator formulas were read.
- `def-weil-module-base-change`: `LinearMap.baseChange` and
  `LinearMap.baseChangeHom`, Mathlib.LinearAlgebra.TensorProduct.Tower. The delivered
  normalization uses the recorded `baseChange`, not a private copy.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme; read at lines 470 and 479. They occur in the
  base scheme and in the affine coordinate interpretation.
- `def-sfb-hopf-action-module-data`: existing `HopfAction.Coassociative` and
  `HopfAction.Counital`, Sheaf.RingTheory.HopfActionModuleData. Their full signatures
  and bodies were read; this landed node is added to stmt_deps.
- `def-sfb-coordinate-hopf-algebra`: the landed definition node owns the existing
  `HopfAction.coordinateHopfAlgebra` instance in
  Sheaf.AlgebraicGeometry.HopfCoactionLinearization. Its definition is the canonical
  Mathlib affine-coordinate Hopf instance specialized to the unbundled field.
  This is the statement dependency needed to type the coaction predicates and
  `HopfAlgebra.antipodeAlgHom` on the coordinate algebra.
- `lem-sfb-hopf-coaction-linearization`: the bijection, morphism, unit and tensor
  clauses remain proof dependencies only. No conclusion of this theorem is used
  to type the statement. The public import of its module also provides the
  coordinate Hopf definition and reexports the module-data, tensor, group-scheme
  and Spec dependencies above.
- The other direct import is Mathlib.LinearAlgebra.FiniteDimensional.Basic, needed
  for the two finite-dimensional binders.

Edge cases checked before drafting and in the second pass:

- V = 0 or W = 0 gives H = 0 and the unique zero coaction, empty basis sums and
  the correct zero Hom comparison. No positive-dimension premise occurs.
- Trivial G gives rho(m) = m tensor 1 and trivial Hom action; every linear map is
  fixed and equivariant, as required.
- For G_m with V and W of weights a and b, the formula gives Hom weight b-a,
  fixing the inverse direction and confirming the order in the conjugation.
- In characteristic p, alpha_p and mu_p are allowed. The universal point in C
  retains nilpotents, unlike tests on field-valued points. This is why the final
  equivalence quantifies over commutative algebras rather than geometric points.
- A = 0 is allowed: both extended modules and Hom are zero and j is the unique
  equivalence. No hypothesis excluding it has been introduced.
- V, W have independent universes; A has arbitrary larger universe, ensuring
  universal-coordinate tests are available. Finite bases do not force these
  vector spaces or test algebras into the field's universe.

Searches for an existing statement:

- msearch.py `leanfinder`, query “Finite dimensional rational modules of an affine
  group scheme have a rational conjugation action on linear Hom whose fixed vectors
  are equivariant maps”: eight hits including
  `Representation.linHom.invariantsEquivFDRepHom`, `FDRep.instFiniteDimensionalHom`,
  and `Representation.linHom.invariantsEquivRepHom`. None supplies a rational
  coordinate coaction for arbitrary affine group schemes.
- msearch.py `leansearch`, query “For rational representations of an affine group
  scheme the linear Hom space is a rational representation with conjugation action”:
  eight hits including `Rep.ihom_obj_ρ_apply`, `Representation.linHom`,
  `Representation.linHom_apply` and `FDRep.dualTensorIsoLinHom`. These are fixed
  abstract-group constructions, not the requested affine-scheme statement.
- msearch.py `loogle`, query
  `Representation.linHom, Coalgebra, TensorProduct.homTensorHomMap`: zero hits.
- msearch.py `grep`, query `Comodule|rational.*[Rr]epresentation|homTensorHom` in
  RepresentationTheory: zero hits from that service.
- Direct rg in Mathlib RepresentationTheory found `Representation.linHom`
  (Basic.lean:663--675) and its invariant/intertwiner results
  (Invariants.lean:190--212). Read their complete definitions and checked why
  rationality is absent. Direct tensor searches found homTensorHomMap and ordinary
  baseChangeHom, neither the rational Hom theorem.
- Direct rg over lean/WeilConjectures and lean/Sheaf for coactions and rational
  representations found the existing HopfAction predicates, the unrestricted
  HopfCoactionLinearization, and RationalRepresentationComoduleDictionary. Read the
  latter; its theorems assume finite type, so they are not substituted for the
  unrestricted node. Its CoordinateComodule abbreviation uses precisely the same
  two HopfAction predicates used here.
- Direct rg for `lem-sfb-rational-linear-hom` in lean/WeilConjectures and
  dag/lean_names_upstream.json found no match. Direct rg for `rationalLinearHom`,
  `coactionPointAction`, and `linearHomBaseChange` in Mathlib and both project roots
  found no duplicate declaration.

Validation: scompile.py NW lem-sfb-rational-linear-hom compiled the delivered
module separately, in both sandbox and actual module mode, against the live
published library. Both checks completed cleanly in about two seconds. Every
variable and universe is explicitly bound; autoImplicit is false; no #check or
other diagnostic commands are left. All Lean lines have at most 100 characters.

## Second reading by NW

This is the dispatcher's worker's own second pass; no other agent was started,
as explicitly required by the brief. The maintainer performs the independent
review of the delivery. I reopened the node JSON and the completed Lean file,
then compared every assumption and conclusion as follows.

The exact hypotheses are field, affine group scheme, two finite-dimensional
vector spaces, and a counital coassociative linear coaction on each. The four
coaction proof binders give exactly two identities per module. No semilinear
algebra-module structure, finite type or characteristic restriction was added.
The chosen coordinate Hopf instance comes from G, not an extra datum.

The conclusion supplies one Hom coaction before quantifying over A, so this is
one rational representation compatible with all extensions, rather than a
separate coaction for each A. The two identities are imposed on that same rho_H.
For every A the linear equivalence j is pinned on all a tensor f, so the symbol
H tensor A = Hom_A in the node is interpreted canonically. The action helper
is the actual evaluated coaction, including the symmetry required by the
base-change dependency. The inner g^-1 action is applied to x first; then j(F);
then the W-action of g. Thus the inverse is neither missing nor on the wrong side.

The fixed-vector test uses f tensor 1 in H tensor C, while the base-changed
f_A is the existing f.baseChange A. The two biconditionals share the identical
coaction square, and the second quantifies over all extended vectors. The
coordinate-point interpretation includes the identity map of C, hence detects
nilpotents and does not silently replace G by its reduced or k-point subgroup.
The zero-dimensional, zero-algebra, trivial-group and weight examples above
still satisfy each clause. The module and the node agree; no mathematical
mismatch or statement correction was found on this pass.

## Repair of returned head 8d802f23ce0a

H2 repaired exactly as requested: replaced
`lem-sfb-hopf-coaction-linearization` in `stmt_deps` with the landed definition
node `def-sfb-coordinate-hopf-algebra`. The theorem remains in `proof_deps`.
I read that definition node's complete statement and existing Lean record, and
reread both `coordinateHopfAlgebra` and `affineCoordinateHopfAlgebra`: their
bodies use the canonical Mathlib instance, without the linearization theorem.
The Lean file, its declarations, its import and its signature are unchanged
from the returned delivery. The earlier report's attribution was corrected.

The current shared main has no Lean record for this item and retains its five
original statement dependencies. Against that main, this packet adds the two
landed definition nodes `def-sfb-hopf-action-module-data` and
`def-sfb-coordinate-hopf-algebra`, and the same delivered Lean record. The
prescribed delivery wrapper rebases the packet on current origin/sheaf-dag.
No mathematical statement, proof plan or proof dependency is changed.

Second reading of the repair: the public signature needs the coaction-law
predicates and the canonical Hopf instance; these are now attributed to their
definition nodes. The linearization theorem is used only by the natural-language
proof steps, and remains a proof dependency. This resolves the sole returned
point while preserving all clauses already accepted by the independent reader.
