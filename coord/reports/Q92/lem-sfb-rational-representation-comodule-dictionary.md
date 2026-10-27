## Worker report

Item: `lem-sfb-rational-representation-comodule-dictionary`, group Q92, stage 2.
The delivery states the full Milne dictionary in
`Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`.
Its five theorems have `sorry` proofs. Its seven helper declarations contain real data:
a natural family of group homomorphisms, the universal coordinate-valued point, the point
of an algebra homomorphism, restriction of the universal action, a subtype of coactions,
and the finite index type and genuine basis used to express GL(V).
All declarations belong to this node's own notions and clauses. There is no independent
missing notion, new node, dependency replacement, or statement correction.

I read the item, all ten original statement-dependency nodes and their recorded interfaces,
the stage-2 brief and conventions, delivery errors H, and the CompactObject example
(which is now withdrawn in favor of its recorded upstream definition). I read Milne's
actual PDF, printed pp.83--84 and 87--89: Chapter 4(a), (24), Remark 4.1 and (25), and
Chapter 4(e). The module docstrings give the node's eleven proof steps, distributed over
the corresponding five theorem declarations. Nothing is proved in this delivery.

Hypothesis and clause correspondence:

- Field k: the explicit section binder `{k : Type u} [Field k]` uses Mathlib `Field`.
- A k-group scheme: `G : Scheme.{u}`, `[G.Over (Spec (.of k))]`, and
  `[GrpObj (G.asOver (Spec (.of k)))]` give the structure map and the actual group-object
  diagrams. This is the recorded `def-sc-group-scheme` interface, unbundled with its
  existing `Scheme.asOver`. Affineness is `[IsAffine G]`.
- Finite type over k: every theorem has
  `[LocallyOfFiniteType (G ↘ Spec (.of k))] [QuasiCompact (G ↘ Spec (.of k))]`, exactly
  the conjunction specified by the recorded finite-type node. The helper notion of a
  natural family does not need this hypothesis; the assertions retain it.
- A=k[G] and its *given* Hopf maps: the coefficient type is literally `Γ(G, ⊤)`.
  `HopfAction.coordinateHopfAlgebra` exposes Mathlib's canonical instance, transported
  from the actual group operations through `G.isoSpec`. This is not an arbitrary Hopf
  structure. Its comultiplication and counit are used in the already defined
  `HopfAction.Coassociative` and `HopfAction.Counital` predicates. The antipode enters
  the proof plan for inverse point operators; it is not an additional hypothesis.
- Arbitrary-dimensional V: `V : Type u`, `[AddCommGroup V] [Module k V]`.
  W has the same binders. There is no dimension hypothesis except on `finite_dictionary`.
- Scalar extension: the action uses `R ⊗[k] V`, the recorded Mathlib convention for
  `def-weil-module-base-change` and Milne's convention on p.83. The node's `V ⊗ R`
  is identified by `TensorProduct.comm`. The generic coaction inserts this symmetry
  explicitly, so its codomain really is `V ⊗[k] Γ(G, ⊤)`.
- A rational representation: `NaturalRepresentation.action` quantifies over every
  commutative k-algebra R in the fixed universe and is a `MonoidHom` to the group
  `R ⊗[k] V ≃ₗ[R] R ⊗[k] V`. Its values are actual R-linear automorphisms, and
  `→*` includes the identity and multiplication laws.
- Naturality: `NaturalRepresentation.naturality` quantifies over every algebra map
  `α : R →ₐ[k] T`, point x and scalar-extended vector z. It equates the two composites
  with `α.toLinearMap.rTensor V`; points change by the existing `points.map`.
- The node's `G(R)=Hom_k-alg(A,R)`: `points` is the actual scheme Hom set.
  `coordinatePoint` sends x through `Spec.mapMulEquiv` and the actual affine isomorphism
  `G.isoSpec.inv`, so this is the recorded Spec/coordinate identification. It has no
  extra choice or witness assumption. `genericPoint` is the point corresponding to id_A.
- Coactions: `CoordinateComodule` is the subtype of all maps `V →ₗ[k] V ⊗[k] Γ(G, ⊤)`
  satisfying the existing coassociativity and counit predicates. Reading their definitions
  gives exactly `(assoc) ∘ (c.rTensor A) ∘ c = (Delta.lTensor V) ∘ c` and
  `rid ∘ (epsilon.lTensor V) ∘ c = id`. Associativity and the unit identification are
  explicit, and neither algebra-linearity of c nor finite-dimensionality is imposed.
- Bijection: `dictionary` asserts an equivalence E of the actual two types.
  Its first conjunct says `(E r).val = genericCoaction G V r`. The latter is the real
  linear composite `comm ∘ restrictScalars(r_A(genericPoint)) ∘ (v ↦ 1 tensor v)`.
  This is precisely `c(v)=r_A(id_A)(v tensor 1)` under the specified symmetry.
- Explicit inverse formula: the second conjunct of `dictionary` quantifies over all
  c, R, x, v, b and every finite presentation `c v = sum_i vi_i tensor ai_i`, and gives
  `(E.symm c).action R (coordinatePoint x) (b tensor v) =
  sum_i (x(ai_i)*b) tensor vi_i`. Switching factors gives the node's formula verbatim.
  Quantifying over every presentation, rather than choosing one, retains independence
  of presentation; n=0 is allowed.
- Linear maps: `intertwines_iff` quantifies over arbitrary r, s and `f : V →ₗ[k] W`.
  Its left side is the intertwining equality for every R and every scheme point, with
  exactly `f.baseChange R`. Its right side is
  `f.rTensor A ∘ genericCoaction r = genericCoaction s ∘ f`.
- Finite dimension and group-scheme morphisms: `finite_dictionary` alone adds
  `[FiniteDimensional k V]`. `finiteBasis` is `Module.finBasis` reindexed by the existing
  `Equiv.ulift.symm` to `ULift (Fin (Module.finrank k V))`. There is no chosen basis
  hypothesis. This identifies GL(V) with the existing general linear scheme.
  The theorem asserts an equivalence between its `RationalHom` morphisms with
  `IsMonHom` and natural families, with the action on every point and *every* vector
  explicitly fixed by `GeneralLinearGroup.homMulEquiv` and the base-changed basis.
  This is a group-scheme statement, not a statement about k-valued points alone.
- Trivial representation: `trivial_coaction` specifies the unique natural family whose
  every point operator is `1`, together with `genericCoaction r v = v tensor 1`.
- Tensor representation: `tensor_coaction` specifies the unique natural family t on
  `V ⊗[k] W` for which the existing `AlgebraTensorModule.distribBaseChange` intertwines
  its action with `TensorProduct.map` of the two actual point automorphisms.
  The second conjunct quantifies over all finite presentations of both coactions and
  states the double sum `(vi tensor wj) tensor (ai*bj)`. Thus t is characterized as the
  actual diagonal tensor action, not merely an arbitrary representation with a formula.
- Universal tensor products: every tensor and tensor map is Mathlib's quotient construction
  and universal maps from the recorded tensor-product node; there is no replacement tensor.
- Sizes: k, G, V, W and test algebras all lie in `Type u`; the generic test algebra
  Γ(G,top) and its tensor square are therefore among them. Natural families live in the
  containing universe. `ULift` puts finite matrix indices in u without excluding the
  empty index. `set_option autoImplicit false` applies to the whole module.

Dependency declarations used, with source interfaces read:

- `Mathlib.Algebra.Field.Defs`: `Field` (lines 171--180).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, and the Hom group through `MonObj`.
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` documents this specialization.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`; signatures and documentation read.
- `Mathlib.AlgebraicGeometry.Group.Affine`: canonical global-section algebra and Hopf
  instances (lines 308--343), `Spec.mapMulEquiv` (lines 267--299), and the corresponding
  `algSpec` construction. `Coalgebra.coassoc`, the two counit axioms,
  `Bialgebra.comulAlgHom`, `Bialgebra.counitAlgHom`, the two antipode axioms and
  `HopfAlgebra.antipodeAlgHom` were read in their Basic/Convolution source modules.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map` (lines 470--484).
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, `.Map`, `.Tower`:
  `TensorProduct`, `mk`, `lift`, `ext'`, `span_tmul_eq_top`, `rTensor`, `comm`, `assoc`,
  `rid`, `LinearMap.baseChange` (Tower:658--691), and `distribBaseChange`
  (Tower:440--473, including both pure-tensor formulas).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie`:
  the recorded standard representation (lines 436--441) is reused through its existing
  general `RationalHom` interface rather than treated as the arbitrary-dimensional
  dictionary. I read `.GeneralLinear.Lie`: `RationalHom` at lines 328--337,
  `RationalHom.points`, and its point/naturality formulas at lines 343--407;
  `.GeneralLinear.Representation`: `RationalHom.representation` at lines 62--73.
  There is no dependency repair: this existing morphism notion is exactly what the
  finite-dimensional clause needs after a genuine basis identification.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes` explicitly reuses the upstream
  `AlgebraicGeometry.GeneralLinearGroup`, coordinate algebra, and natural `homMulEquiv`.
  I read that module and the original `.GroupScheme.GeneralLinear` definition and
  `homMulEquiv` (lines 46--78). The statement uses that same GL, including empty rank;
  it does not construct another general linear scheme or need the SL clauses.
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: `FiniteDimensional` (lines 73--77);
  `.Dimension.Free`: `Module.finBasis`; `.TensorProduct.Basis`: `Basis.baseChange`;
  `.Matrix.GeneralLinearGroup.Defs`: `Matrix.GeneralLinearGroup.toLin'` (lines 107--116).
- Added *landed* dependencies `def-sfb-hopf-action-module-data` and
  `def-sfb-affine-coordinate-hopf-algebra`: their existing source gives
  `HopfAction.Coassociative`, `HopfAction.Counital`, and
  `HopfAction.coordinateHopfAlgebra`. Both nodes and their sources were read.
  This uses the brief's permission for stmt_deps to gain already landed nodes and
  avoids duplicating those definitions. Neither depends on this item, and no cycle is added.
- Proof-only imports retain `Mathlib.CategoryTheory.Yoneda` (`Yoneda.fullyFaithful`),
  `Mathlib.AlgebraicGeometry.Pullbacks` (`pullbackSpecIso` and projections), and
  `Mathlib.RingTheory.TensorProduct.Maps` (`productMap` and pure-tensor formula).
  The relevant signatures and documentation were read for the proof plan.

Searches actually run (the wrapper records are in `searches.jsonl`):

- LeanFinder: "Rational representations of an affine group scheme correspond to coordinate
  Hopf algebra comodules in arbitrary dimension". Eight hits, all affine-space coordinates
  and affine-space equivalences; none states the dictionary.
- Loogle: `"Comodule"`. Zero hits.
- Mathlib grep: `Comodule|coaction|rational.*representation|representation.*Hopf`.
  Zero hits in the wrapper's search. Separate source reading confirms `Coalgebra.Repr`
  is a finite presentation of a comultiplication, not a comodule representation.
- LeanSearch: "Natural representations of affine group schemes are equivalent to right
  comodules over the coordinate Hopf algebra". Eight hits: `Coalgebra.Repr`, affine-scheme
  category equivalences, and generic coalgebra/Hopf category facts. None is this statement.
- `grep -rn` for the exact item id in `lean/WeilConjectures`: no matches.
- `rg` in upstream for `RationalHom`, `representation`, `Comodule`, `coaction`:
  finite matrix scheme morphisms and unrelated faithfully-flat descent coactions;
  no arbitrary-dimensional natural-family/comodule correspondence.
- `rg` in `lean/Sheaf` for the same notions: the existing HopfAction predicates and
  coordinate instance were reused. FiniteComoduleCoefficientCoalgebra is a theorem
  about coefficients, not this dictionary. RhoSectionModuleData defines a special
  finite-dimensional left-translation condition; LinearlyReductiveGroupScheme uses
  finite matrix representations. Neither defines general natural families.
- Collision search for `NaturalRepresentation`, `genericCoaction`, `CoordinateComodule`
  and the full main declaration in Mathlib, upstream, project and upstream name index:
  no declarations with these full names. No second notion is being introduced.

Edge cases checked against the statements and actual constructions: V=0 and W=0;
finite rank zero (the basis and matrix index are empty, with no `[Nonempty]` assumption);
empty finite tensor presentations; infinite-dimensional spaces (finite presentations are
per vector, not uniform); the trivial group; arbitrary characteristic; nonreduced affine
groups and nonreduced test algebras; the zero test algebra. No density of rational points,
reducedness, smoothness, algebraic closedness or characteristic-zero assumption is used.
The identity and the generic tensor-square tests are included in the chosen test universe.

Validation: the final module compiled with `scompile.py` in both its sandbox and library
names, taking 14.7 s and 11.0 s, with no errors or non-sorry warnings. Earlier diagnostics
were removed. No local Lean invocation, global build, or live repository mutation was used.
There is no `STATEMENT-DISPUTED` issue.

## Second reading by Q92

This is a second pass by the same dispatched worker; no other agent was started, as required
by the dispatch. The maintainer's separate review remains independent. I reopened the item
and the final module, compared every hypothesis and clause above, and checked the following
potential mismatches specifically:

1. The original ten statement dependencies already provide the needed mathematical notions.
   The algebraic-representation record is not the dictionary, but its imported `RationalHom`
   is exactly the finite-dimensional scheme-map notion; no specialization was substituted
   for the arbitrary-dimensional natural-family definition.
2. Scalar-factor order differs from the node's notation only by the *recorded* symmetry.
   `genericCoaction` includes the actual symmetry and the evaluation formula has
   `(x(ai)*b) tensor vi`, so the coefficient multiplication and action order agree.
3. I checked `HopfAction.Coassociative` and `Counital` again: the right-comodule order
   and the unit identification are the exact ones in Milne (24). These were reused,
   not written as a new private predicate.
4. A finite basis is constructed, not assumed. The lifted empty basis works at dimension
   zero. Every algebra-valued point and every scalar-extended vector is in the finite
   comparison, so no k-points-only interpretation was introduced.
5. The trivial and tensor families are pinned by their actual point actions. Tensor
   coactions alone do not stand in for tensor actions. I corrected the tensor theorem's
   proof docstring to match Mathlib's precise `distribBaseChange` orientation:
   `b tensor (v tensor w)` maps to `(b tensor v) tensor_R (1 tensor w)`.
6. Every theorem retains the node's finite-type conjunction and every definition has real
   data. All universes are explicit, including the universe of finite matrix indices.
7. I fixed all line-length warnings, removed every `#check`/`#synth` diagnostic, checked
   the main recorded signature against the file verbatim and included all twelve public
   declarations in the record. Added statement dependencies name the reused landed APIs;
   the accepted natural-language statement and proof are unchanged.

## Return repair: H2 dependency ownership

The immutable-head review at `140a2910b0fe` returned one issue: the added
`lem-sfb-hopf-coaction-linearization` statement dependency was a theorem node,
but this module uses its plain coordinate Hopf instance, not its theorem conclusion.
Replaced that added dependency by the already landed definition node
`def-sfb-affine-coordinate-hopf-algebra` (Q08, 2026-10-24). Its `existing: true`
record owns `HopfAction.affineCoordinateHopfAlgebra` and
`HopfAction.coordinateHopfAlgebra` in the unchanged module
`Sheaf.AlgebraicGeometry.HopfCoactionLinearization`. I read that definition node's
statement and full Lean record, and both definitions and their docstrings in the
recorded module. The first definition is the canonical Mathlib instance obtained
by `inferInstance`; the second specializes it to the unbundled field. Neither
uses the postponed linearization theorem. No declaration was moved or duplicated.
`def-sfb-hopf-action-module-data` remains a statement dependency and still owns
the `HopfAction.Coassociative` and `HopfAction.Counital` predicates.

The prescribed initial dry run of the saved packet passed at `f6504752ffd`;
that mechanical pass preceded this required semantic repair. Compared the saved
node with the refreshed read clone: only `lean` and `stmt_deps` differ. The
accepted statement and proof remain identical. The repaired packet introduces
no new node, dependency module, statement correction, or Lean source change.

For the repair self-check I reopened the entire final Lean module and the node.
The natural-family structure, generic coordinate point, both dictionary formulas,
intertwiner equivalence, finite-dimensional scheme comparison, and uniquely pinned
trivial and tensor actions are unchanged from the independently accepted reading.
The owning definition imposes no extra finite-type or nonzero hypothesis; hence
the checked zero-space, rank-zero, infinite-dimensional, zero-algebra and nonreduced
cases are retained. This is the same dispatched worker's second reading; no other
agent was started. The only fault found and repaired was the added theorem-node
dependency described above.
