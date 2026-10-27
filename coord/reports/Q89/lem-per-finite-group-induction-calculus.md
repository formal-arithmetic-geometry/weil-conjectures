## Worker report

The module `Sheaf.RepresentationTheory.FiniteGroupInductionCalculus` states the whole
node as `Rep.QuotientInduction.finiteGroupInductionCalculus`, with one `sorry` and
no proved theorem. Its eight helpers have explicit data or are abbreviations of
existing constructions. The natural-language statement is unchanged. The only
additional statement dependency is the already landed
`def-per-finite-module-split-grothendieck`, used under brief-stage2 §5's permission
to cite a landed definition. No dependency record is repaired and no new DAG node
is introduced.

Hypotheses and objects, clause by clause:

- `F : Type u`, `[Field F] [IsAlgClosed F] [CharZero F]` give exactly an
  algebraically closed characteristic-zero field. No particular algebraic closure
  or embedding is chosen.
- `G : Type u`, `[Group G] [Finite G]`, `H K : Subgroup G`, and `hKH : K ≤ H`
  give all finite groups and the specified nested subgroups. `Subgroup.inclusion
  hKH`, `H.subtype`, and `K.subtype` are the existing inclusion homomorphisms.
- `W : FDRep F H`, `U : FDRep F K`, and `V : FDRep F G` occur universally in
  their respective clauses. Mathlib FDRep carries precisely a finite-dimensional
  module and a representation. For groups, a homomorphism into endomorphisms has
  inverse at g given by the action at g⁻¹, so this is exactly the GL-valued notion.
- The construction `ind φ W` is `FDRep.of (Representation.ind φ W.ρ)`.
  Mathlib takes the coinvariants of the diagonal H-action on F[G] ⊗ W and
  acts on the group-algebra index by right inverse translation. Our `mk φ W g`
  is `Representation.IndV.mk φ W.ρ g⁻¹`, so it represents exactly `[g,w]` in
  the node's convention. Inverting the basis index sends Mathlib's relation
  `[h g⁻¹, hw] = [g⁻¹,w]` to the displayed relation `[gh,w]=[g,hw]`.
  This is a reindexing of the quotient presentation, with the specified action,
  rather than another arbitrary induction model. The first two conjuncts state
  the balancing relation and left action explicitly. F[G] itself is Mathlib
  `MonoidAlgebra F G`, whose singletons have the required basis and multiplication.
- Restriction `res φ V` keeps V and composes its existing action with φ.
  In categorical statements the existing `Rep.res` and `Rep.resFunctor` are used.
- The finite-direct-sum clause quantifies over every finite `I : Type u`, including
  empty I. `sum W` bundles `Representation.directSum`; the isomorphism sends the
  generator attached to `DirectSum.lof ... i w` to the i-th inclusion of `[g,w]`.
  This both asserts preservation of the actual direct sum and identifies its
  canonical comparison.
- The dimension clause is exactly `Module.finrank F (ind H.subtype W) =
  H.index * Module.finrank F W`. Finite dimension of induction is already supplied
  by the existing instances used to construct its FDRep object.
- Transitivity is the family `t U` of representation isomorphisms. Its generator
  equation is `[g,[h,w]] ↦ [gh,w]`. Its next equation is naturality with respect
  to every intertwiner `f : rep U ⟶ rep U'`, using `Rep.indMap` twice on the
  left and once on the right.
- The representation-level tensor identity is `p V W`. It has the stated source
  V ⊗ Ind W and target Ind(Res V ⊗ W), before any coinvariants are applied to
  their tensor products. Its normalization is `v ⊗ [g,w] ↦ [g,g⁻¹v ⊗ w]`;
  its second clause is naturality in both variables for all intertwiners f and q.
- Frobenius reciprocity is the family `E W V` of F-linear equivalences on
  equivariant Hom spaces. The equation `(E W V f).hom w = f.hom (mk ... 1 w)`
  is exactly evaluation at `[1] ⊗ w`. The next equation states naturality for
  precomposition in W and postcomposition in V, including the specified induction
  and restriction maps. This clause can use `Rep.indResHomEquiv` in stage 3.
- The presentation `group F J` reuses
  `RepresentationTheory.FiniteModuleSplitGrothendieck F (MonoidAlgebra F J)`.
  The existing `FiniteAlgebraModule` identifies representations with finite
  group-algebra modules by `Representation.asAlgebraHom`; `algebraModule` supplies
  exactly this action and `cls` is its actual quotient generator. The pre-existing
  presentation identifies isomorphic modules and imposes the direct-sum relations,
  which is the same presentation as free abelian on isomorphism classes with
  `[A ⊕ B]=[A]+[B]`. No choice of representatives or second presentation is used.
- `m J : group F J →+ group F J →+ group F J` is a biadditive multiplication,
  characterized by `m J (cls A) (cls B) = cls (A ⊗ B)`. Associativity,
  commutativity and the trivial-line unit are stated explicitly, spelling out the
  representation-ring structure already implicit in the node. Addition is the
  existing addition of the presented abelian group.
- `r J L` and `i J L` are additive maps on these actual presented groups, with
  generator formulas for restriction and induction. `iKH` is induction along the
  actual inclusion K → H; its generator formula avoids silently identifying K
  with the separately typed subgroup `K.subgroupOf H`.
- The final equations state the tensor identity for every `x : group F H`, not
  just generator classes, and transitivity as equality of additive maps
  `(i G H).comp iKH = i G K`. They therefore cover arbitrary negative virtual
  classes as well.

The single universe u is a common ambient set universe containing coefficients,
groups, finite-dimensional vector spaces and finite indexing sets, as in Mathlib
FDRep. It is arbitrary; there is no finiteness-of-the-field assumption or bound
on dimensions or finite cardinalities. Finite-dimensional isomorphism classes
have representatives on F^n in this universe, including classes in the existing
split presentation. Its quotient of a free group has the natural larger universe.
`open Classical in` on the theorem provides decidable equality for the existing
DirectSum inclusions; it is not a new hypothesis or a custom local notation.

Dependency declarations read and reused:

- `def-weil-algebraic-closure`: `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic (class and its root interpretation read).
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional = Module.Finite`,
  Mathlib.LinearAlgebra.FiniteDimensional.Defs; carried by Mathlib FDRep.of.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and its bilinear generators,
  Mathlib.LinearAlgebra.TensorProduct.Defs; diagonal actions use
  Representation.tprod and the existing monoidal structures.
- `def-weil-pbc-quotient-module`: `Submodule.mkQ` and quotient module instances,
  Mathlib.LinearAlgebra.Quotient.Defs, used by Representation.Coinvariants.
- `def-weil-pbc-direct-sum-modules`: `DirectSum`, its module structure and
  `DirectSum.lof`, Mathlib.Algebra.DirectSum.Module; action is
  Representation.directSum from Mathlib.RepresentationTheory.Basic.
- `def-weil-vector-space-dimension`: `Module.finrank`,
  Mathlib.LinearAlgebra.Dimension.Finrank, returning the finite basis cardinality.
- `def-trf-abelian-group-presentation`: `Module.Relations.Quotient`,
  Mathlib.Algebra.Module.Presentation.Basic. Its free-module quotient convention
  agrees with the existing split presentation (FreeAbelianGroup modulo the
  generated subgroup); the import is retained for the stage-3 descent argument.
- Added landed dependency `def-per-finite-module-split-grothendieck`:
  `FiniteAlgebraModule`, `FiniteModuleSplitGrothendieck`, and its actual quotient
  relations from Sheaf.RepresentationTheory.FiniteModuleSplitGrothendieck.
- Proof dependencies `lem-weil-pbc-vector-space-free` and
  `lem-sc-tensor-product-free-basis` are the Mathlib leaves
  `Module.Free.of_divisionRing` and `Module.Basis.tensorProduct`.
  Their modules are imported privately for stage 3. No proof imports are omitted
  for an import cycle.

Searches made (all run, not inferred):

- msearch leanfinder: "Induction of finite dimensional representations transitivity
  tensor identity Frobenius reciprocity representation ring" returned eight hits,
  including Representation.ind_apply, FDRep.of_ρ and coinvariantsTensorIndIso.
  None states the full item; coinvariantsTensorIndIso has already taken
  coinvariants and does not state our representation-level tensor identity.
- msearch loogle: "Rep.indResHomEquiv, Representation.ind" returned
  Rep.indResHomEquiv_symm_apply. Read the full Induced.lean construction,
  indResHomEquiv and indResAdjunction; they cover Frobenius, not the full calculus.
- msearch grep: "ind.*[Tt]ensor|ind.*[Tt]rans|[Rr]epresentationRing" in
  RepresentationTheory returned 12 hits for induction/coinvariant tensor and
  intertwiner constructions, no full calculus or representation-ring presentation.
- msearch leansearch: "The representation ring of a finite group is presented by
  isomorphism classes of finite dimensional representations modulo direct sum
  relations" returned FDRep and directSum infrastructure, not the presentation.
- rg of Mathlib RepresentationTheory for FDRep, induction, tensor comparisons and
  representation rings located the existing finite-dimensional category and all
  quotient/representation signatures used here. Full source signatures/docstrings
  were read, including the nonstandard group-index convention.
- rg of lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found no
  full induction-calculus theorem or collision with the declared namespace/names.
  The item-id search found the already landed BrauerMonomialInduction consumer,
  whose docstring independently uses the same inverse-index convention.
- Concept search in project sources located FiniteModuleSplitGrothendieck, and
  the DAG search located its existing definition node; both were read and reused.
  This avoided a duplicate representation-group construction.

Sources and edge cases:

Read the current blueprint proof of lem-per-artin-gabber-affine-curve. Its Step 3
is Verdier-duality context and does not prove the inherited auxiliary representation
identities; consistent with the node's source and proof_origin, the thirteen-step
proof in the accepted node is the actual proof plan. Serre remains WANTED; no
unavailable source is represented as having been read.

Checked zero W, zero U and zero V; the empty direct sum; H=G; H the trivial
subgroup; K=H and K trivial; the trivial ambient group; one-dimensional nontrivial
characters; and negative virtual classes. The zero-space dimension formula is
0=[G:H]·0. For empty I both sides of the sum comparison are zero and its generator
clause is vacuous, while existence of the isomorphism still asserts the result.
For H=G the balancing relation identifies `[g,w]` with `[1,gw]`; for H trivial,
induction has the regular copies of W. The inverse-index convention gives the
correct tensor formula for nontrivial characters. There are no disputed
statements or natural-language statement corrections.

Validation: scompile.py compiled the final named library module and its isolated
sandbox probe cleanly, with no warnings. Exactly the main theorem is postponed;
all helper data is explicit. The required deliver2.py dry run follows this report.

Process note: one early, discarded diagnostic was mistakenly run directly with
lake env lean and a scratch file outside the prescribed sandbox. It did not edit
the shared source or any library file. Subsequent probes and every compile of the
delivered module used scompile.py exclusively. No Git command was run by the
worker in the shared repository. The obsolete diagnostic is not part of delivery.

## Second reading by Q89

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
